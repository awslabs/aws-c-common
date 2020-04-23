/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/allocator.h>
#include <aws/common/array_list.h>
#include <aws/common/assert.h>

#ifdef WIN32
#    include <malloc.h>
#elif __linux__ || __APPLE__
#    include <stdlib.h>
#endif

#if defined(PAGE_SIZE) && !defined(AWS_SBA_PAGE_SIZE)
#    define AWS_SBA_PAGE_SIZE ((uintptr_t)(PAGE_SIZE))
#else
#    if !defined(AWS_SBA_PAGE_SIZE)
#        define AWS_SBA_PAGE_SIZE ((uintptr_t)(4096))
#    endif
#endif

#define AWS_SBA_PAGE_MASK ((uintptr_t) ~(AWS_SBA_PAGE_SIZE - 1))
#define AWS_SBA_TAG_VALUE 0x736f6d6570736575ULL

/* list of sizes of bins, must be powers of 2, and less than AWS_SBA_PAGE_SIZE * 0.5 */
#define AWS_SBA_BIN_COUNT 5
static const size_t s_bin_sizes[AWS_SBA_BIN_COUNT] = {32, 64, 128, 256, 512};
static const size_t s_max_bin_size = 512;

struct free_bin {
    size_t size;                  /* size of allocs in this bin */
    uint8_t *page_cursor;         /* pointer to working page, currently being chunked from */
    struct aws_array_list pages;  /* all pages in use by this bin, could be optimized at scale by being a set */
    struct aws_array_list chunks; /* free chunks available in this bin */
};

/* Header stored at the base of each page.
 * As long as this is under 32 bytes, all is well.
 * Above that, there's potentially more waste per page */
struct page_header {
    uint64_t tag;         /* marker to identify/validate pages */
    struct free_bin *bin; /* bin this page belongs to */
    uint32_t alloc_count; /* number of outstanding allocs from this page */
};

/* This is the impl for the aws_allocator */
struct small_block_allocator {
    struct aws_allocator *allocator; /* parent allocator, for large allocs */
    struct free_bin bins[AWS_SBA_BIN_COUNT];
    size_t used; /* memory in use */
};

static void *s_page_base(const void *addr) {
    /* mask off the address to round it to page alignment */
    uint8_t *page_base = (uint8_t *)(((uintptr_t)addr) & AWS_SBA_PAGE_MASK);
    return page_base;
}

static void *s_page_bind(void *addr, struct free_bin *bin) {
    /* insert the header at the base of the page and advance past it */
    struct page_header *page = (struct page_header *)addr;
    page->tag = AWS_SBA_TAG_VALUE;
    page->bin = bin;
    page->alloc_count = 0;
    return (uint8_t *)addr + sizeof(struct page_header);
}

static void *s_aligned_alloc(size_t size, size_t align) {
#ifdef WIN32
    return _aligned_malloc(size, align);
#else
    void *mem = NULL;
    int return_code = posix_memalign(&mem, align, size);
    if (return_code) {
        aws_raise_error(AWS_ERROR_OOM);
        return NULL;
    }
    return mem;
#endif
}

static void s_aligned_free(void *addr) {
#ifdef WIN32
    _aligned_free(addr);
#else
    free(addr);
#endif
}

static void *s_sba_mem_acquire(struct aws_allocator *allocator, size_t size);
static void s_sba_mem_release(struct aws_allocator *allocator, void *ptr);
static void *s_sba_mem_realloc(struct aws_allocator *allocator, void *old_ptr, size_t old_size, size_t new_size);
static void *s_sba_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size);

static struct aws_allocator s_sba_allocator = {
    .mem_acquire = s_sba_mem_acquire,
    .mem_release = s_sba_mem_release,
    .mem_realloc = s_sba_mem_realloc,
    .mem_calloc = s_sba_mem_calloc,
};

static int s_sba_init(struct small_block_allocator *sba, struct aws_allocator *allocator) {
    sba->allocator = allocator;
    for (unsigned idx = 0; idx < AWS_SBA_BIN_COUNT; ++idx) {
        struct free_bin *bin = &sba->bins[idx];
        bin->size = s_bin_sizes[idx];
        if (aws_array_list_init_dynamic(&bin->pages, sba->allocator, 16, sizeof(void *))) {
            return AWS_OP_ERR;
        }
        /* start with enough chunks for 1 page */
        if (aws_array_list_init_dynamic(
                &bin->chunks, sba->allocator, aws_max_size(AWS_SBA_PAGE_SIZE / bin->size, 16), sizeof(void *))) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}

static void s_sba_clean_up(struct small_block_allocator *sba) {
    /* free all known pages, then free the working page */
    for (unsigned idx = 0; idx < AWS_SBA_BIN_COUNT; ++idx) {
        struct free_bin *bin = &sba->bins[idx];
        for (size_t page_idx = 0; page_idx < bin->pages.length; ++page_idx) {
            void *page_addr = NULL;
            aws_array_list_get_at(&bin->pages, &page_addr, page_idx);
            s_aligned_free(page_addr);
        }
        if (bin->page_cursor) {
            void *page_addr = s_page_base(bin->page_cursor);
            s_aligned_free(page_addr);
        }

        aws_array_list_clean_up(&bin->pages);
        aws_array_list_clean_up(&bin->chunks);
    }
}

struct aws_allocator *aws_allocator_sba_new(struct aws_allocator *allocator) {
    struct small_block_allocator *sba = NULL;
    struct aws_allocator *sba_allocator = NULL;
    aws_mem_acquire_many(
        allocator, 2, &sba, sizeof(struct small_block_allocator), &sba_allocator, sizeof(struct aws_allocator));

    AWS_FATAL_ASSERT(sba_allocator);
    AWS_FATAL_ASSERT(sba);

    AWS_ZERO_STRUCT(*sba);
    AWS_ZERO_STRUCT(*sba_allocator);

    /* copy the template vtable */
    *sba_allocator = s_sba_allocator;
    sba_allocator->impl = sba;

    if (s_sba_init(sba, allocator)) {
        s_sba_clean_up(sba);
        aws_mem_release(allocator, sba);
        return NULL;
    }
    return sba_allocator;
}

void aws_allocator_sba_destroy(struct aws_allocator *sba_allocator) {
    struct small_block_allocator *sba = sba_allocator->impl;
    struct aws_allocator *allocator = sba->allocator;
    s_sba_clean_up(sba);
    aws_mem_release(allocator, sba);
}

static void *s_sba_alloc_from_bin(struct free_bin *bin) {
    /* check the free list, hand chunks out in FIFO order */
    if (aws_array_list_length(&bin->chunks) > 0) {
        void *chunk = NULL;
        if (aws_array_list_back(&bin->chunks, &chunk)) {
            return NULL;
        }
        AWS_FATAL_ASSERT(chunk);
        struct page_header *page = s_page_base(chunk);
        page->alloc_count++;
        return chunk;
    }

    /* If there is a working page to chunk from, use it */
    if (bin->page_cursor) {
        struct page_header *page = s_page_base(bin->page_cursor);
        AWS_FATAL_ASSERT(page);
        size_t space_left = AWS_SBA_PAGE_SIZE - (bin->page_cursor - (uint8_t *)page);
        if (space_left >= bin->size) {
            void *chunk = bin->page_cursor;
            page->alloc_count++;
            bin->page_cursor += bin->size;
            space_left -= bin->size;
            if (space_left < bin->size) {
                aws_array_list_push_back(&bin->pages, page);
                bin->page_cursor = NULL;
            }
            return chunk;
        }
    }

    /* Nothing free to use, allocate a page and restart */
    uint8_t *new_page = s_aligned_alloc(AWS_SBA_PAGE_SIZE, AWS_SBA_PAGE_SIZE);
    new_page = s_page_bind(new_page, bin);
    bin->page_cursor = new_page;
    return s_sba_alloc_from_bin(bin);
}

static void s_sba_free_to_bin(struct free_bin *bin, void *addr) {
    AWS_FATAL_ASSERT(addr);
    struct page_header *page = s_page_base(addr);
    AWS_FATAL_ASSERT(page->bin == bin);
    page->alloc_count--;
    if (page->alloc_count == 0 && page != s_page_base(bin->page_cursor)) { /* empty page, free it */
        uint8_t *page_start = (uint8_t *)page + sizeof(struct page_header);
        uint8_t *page_end = page_start + AWS_SBA_PAGE_SIZE;
        /* Remove all chunks in the page from the free list */
        intptr_t chunk_idx = bin->chunks.length;
        for (; chunk_idx >= 0; --chunk_idx) {
            uint8_t *chunk = NULL;
            aws_array_list_get_at(&bin->chunks, &chunk, chunk_idx);
            if (chunk >= page_start && chunk < page_end) {
                aws_array_list_swap(&bin->chunks, chunk_idx, bin->chunks.length - 1);
                aws_array_list_pop_back(&bin->chunks);
            }
        }

        /* Find page in pages list and remove it */
        for (size_t page_idx = 0; page_idx < bin->pages.length; ++page_idx) {
            void *page_addr = NULL;
            aws_array_list_get_at(&bin->pages, &page_addr, page_idx);
            if (page_addr == page) {
                aws_array_list_swap(&bin->pages, page_idx, bin->pages.length - 1);
                aws_array_list_pop_back(&bin->pages);
                break;
            }
        }
        s_aligned_free(page);
        return;
    }

    aws_array_list_push_back(&bin->chunks, addr);
}

static struct free_bin *s_sba_find_bin(struct small_block_allocator *sba, size_t size) {
    AWS_PRECONDITION(size < s_max_bin_size);
    for (unsigned idx = 0; idx < AWS_SBA_BIN_COUNT; ++idx) {
        struct free_bin *bin = &sba->bins[idx];
        if (bin->size >= size) {
            return bin;
        }
    }
    /* should never get here */
    AWS_POSTCONDITION(false);
    return NULL;
}

static void *s_sba_alloc(struct small_block_allocator *sba, size_t size) {
    if (size <= s_max_bin_size) {
        struct free_bin *bin = s_sba_find_bin(sba, size);
        AWS_FATAL_ASSERT(bin);
        sba->used += bin->size;
        return s_sba_alloc_from_bin(bin);
    }
    return aws_mem_acquire(sba->allocator, size);
}

static void s_sba_free(struct small_block_allocator *sba, void *addr) {
    if (!addr) {
        return;
    }

    struct page_header *page = (struct page_header *)s_page_base(addr);
    if (page->tag == AWS_SBA_TAG_VALUE) {
        s_sba_free_to_bin(page->bin, addr);
        return;
    }
    /* large alloc, give back to underlying allocator */
    aws_mem_release(sba->allocator, addr);
}

static void *s_sba_mem_acquire(struct aws_allocator *allocator, size_t size) {
    struct small_block_allocator *sba = allocator->impl;
    return s_sba_alloc(sba, size);
}

static void s_sba_mem_release(struct aws_allocator *allocator, void *ptr) {
    struct small_block_allocator *sba = allocator->impl;
    s_sba_free(sba, ptr);
}

static void *s_sba_mem_realloc(struct aws_allocator *allocator, void *old_ptr, size_t old_size, size_t new_size) {
    struct small_block_allocator *sba = allocator->impl;
    /* If both allocations come from the parent, let the parent do it */
    if (old_size > s_max_bin_size && new_size > s_max_bin_size) {
        void *new_mem = old_ptr;
        if (aws_mem_realloc(sba->allocator, &new_mem, old_size, new_size)) {
            return NULL;
        }
    }

    /* Either both small allocs, or one small, one large */
    void *new_mem = s_sba_alloc(sba, new_size);
    memcpy(new_mem, old_ptr, aws_min_size(old_size, new_size));
    s_sba_free(sba, old_ptr);
    return new_mem;
}

static void *s_sba_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    struct small_block_allocator *sba = allocator->impl;
    void *mem = s_sba_alloc(sba, size * num);
    memset(mem, 0, size * num);
    return mem;
}
