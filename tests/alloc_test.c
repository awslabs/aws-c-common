/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

#include <aws/common/array_list.h>
#include <aws/common/assert.h>
#include <aws/common/thread.h>
#include <aws/testing/aws_test_harness.h>

#ifdef __MACH__
#    include <CoreFoundation/CoreFoundation.h>
#endif

static void *s_test_alloc_acquire(struct aws_allocator *allocator, size_t size) {
    (void)allocator;
    return (size > 0) ? malloc(size) : NULL;
}

static void s_test_alloc_release(struct aws_allocator *allocator, void *ptr) {
    (void)allocator;
    free(ptr);
}

static void *s_test_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    (void)allocator;
    (void)oldsize;
    /* Realloc should ensure that newsize is never 0 */
    AWS_FATAL_ASSERT(newsize != 0);
    return realloc(ptr, newsize);
}

static void *s_test_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    (void)allocator;
    return (num > 0 && size > 0) ? calloc(num, size) : NULL;
}

/**
 * Check that we correctly protect against
 * https://wiki.sei.cmu.edu/confluence/display/c/MEM04-C.+Beware+of+zero-length+allocations
 * For now, can only test the realloc case, because it returns NULL on error
 * Test the remaining cases once https://github.com/awslabs/aws-c-common/issues/471 is solved
 */
AWS_TEST_CASE(test_alloc_nothing, s_test_alloc_nothing_fn)
static int s_test_alloc_nothing_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_allocator test_allocator = {
        .mem_acquire = s_test_alloc_acquire,
        .mem_release = s_test_alloc_release,
        .mem_realloc = s_test_realloc,
        .mem_calloc = s_test_calloc,
    };

    /* realloc should handle the case correctly, return null, and free the memory */
    void *p = aws_mem_acquire(&test_allocator, 12);
    ASSERT_SUCCESS(aws_mem_realloc(&test_allocator, &p, 12, 0));
    ASSERT_NULL(p);
    return 0;
}

/*
 * Small Block Allocator tests
 */
static int s_sba_alloc_free_once(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, false);
    void *mem = aws_mem_acquire(sba, 42);
    ASSERT_NOT_NULL(mem);
    const size_t allocated = aws_mem_tracer_bytes(allocator);
    ASSERT_TRUE(allocated > 0);
    aws_mem_release(sba, mem);
    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_alloc_free_once, s_sba_alloc_free_once)

#define NUM_TEST_ALLOCS 10000
#define NUM_TEST_THREADS 8
static int s_sba_random_allocs_and_frees(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, false);
    srand(42);

    void *allocs[NUM_TEST_ALLOCS];
    for (size_t count = 0; count < NUM_TEST_ALLOCS; ++count) {
        size_t size = aws_max_size(rand() % 512, 1);
        void *alloc = aws_mem_acquire(sba, size);
        ASSERT_NOT_NULL(alloc);
        allocs[count] = alloc;
    }

    for (size_t count = 0; count < NUM_TEST_ALLOCS; ++count) {
        void *alloc = allocs[count];
        aws_mem_release(sba, alloc);
    }

    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_random_allocs_and_frees, s_sba_random_allocs_and_frees)

static int s_sba_random_reallocs(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, false);
    srand(128);

    void *alloc = NULL;
    size_t size = 0;
    for (size_t count = 0; count < NUM_TEST_ALLOCS; ++count) {
        size_t old_size = size;
        size = rand() % 4096;
        ASSERT_SUCCESS(aws_mem_realloc(sba, &alloc, old_size, size));
    }
    ASSERT_SUCCESS(aws_mem_realloc(sba, &alloc, size, 0));

    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_random_reallocs, s_sba_random_reallocs)

struct allocator_thread_test_data {
    struct aws_allocator *test_allocator;
    uint32_t thread_idx;
};

static void s_threaded_alloc_worker(void *user_data) {
    struct aws_allocator *test_allocator = ((struct allocator_thread_test_data *)user_data)->test_allocator;

    void *allocs[NUM_TEST_ALLOCS];
    for (size_t count = 0; count < NUM_TEST_ALLOCS / NUM_TEST_THREADS; ++count) {
        size_t size = aws_max_size(rand() % 512, 1);
        void *alloc = aws_mem_acquire(test_allocator, size);
        AWS_FATAL_ASSERT(alloc);
        allocs[count] = alloc;
    }

    for (size_t count = 0; count < NUM_TEST_ALLOCS / NUM_TEST_THREADS; ++count) {
        void *alloc = allocs[count];
        aws_mem_release(test_allocator, alloc);
    }
}

static void s_thread_test(
    struct aws_allocator *allocator,
    void (*thread_fn)(void *),
    struct aws_allocator *test_allocator) {
    const struct aws_thread_options *thread_options = aws_default_thread_options();
    struct aws_thread threads[NUM_TEST_THREADS];
    struct allocator_thread_test_data thread_data[NUM_TEST_THREADS];
    AWS_ZERO_ARRAY(threads);
    AWS_ZERO_ARRAY(thread_data);
    for (size_t thread_idx = 0; thread_idx < AWS_ARRAY_SIZE(threads); ++thread_idx) {
        struct aws_thread *thread = &threads[thread_idx];
        aws_thread_init(thread, allocator);
        struct allocator_thread_test_data *data = &thread_data[thread_idx];
        data->test_allocator = test_allocator;
        data->thread_idx = (uint32_t)thread_idx;
        aws_thread_launch(thread, thread_fn, data, thread_options);
    }

    for (size_t thread_idx = 0; thread_idx < AWS_ARRAY_SIZE(threads); ++thread_idx) {
        struct aws_thread *thread = &threads[thread_idx];
        aws_thread_join(thread);
    }
}

static int s_sba_threaded_allocs_and_frees(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(96);

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, true);

    s_thread_test(allocator, s_threaded_alloc_worker, sba);

    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_threaded_allocs_and_frees, s_sba_threaded_allocs_and_frees)

static void s_threaded_realloc_worker(void *user_data) {
    struct allocator_thread_test_data *thread_data = user_data;
    struct aws_allocator *test_allocator = thread_data->test_allocator;
    void *alloc = NULL;
    size_t size = 0;
    for (size_t count = 0; count < NUM_TEST_ALLOCS / NUM_TEST_THREADS; ++count) {
        size_t old_size = size;
        size = rand() % 1024;
        if (old_size) {
            AWS_FATAL_ASSERT(0 == memcmp(alloc, &thread_data->thread_idx, 1));
        }
        AWS_FATAL_ASSERT(0 == aws_mem_realloc(test_allocator, &alloc, old_size, size));
        /* If there was a value, make sure it's still there */
        if (old_size && size) {
            AWS_FATAL_ASSERT(0 == memcmp(alloc, &thread_data->thread_idx, 1));
        }
        if (size) {
            memset(alloc, (int)thread_data->thread_idx, size);
        }
    }
    AWS_FATAL_ASSERT(0 == aws_mem_realloc(test_allocator, &alloc, size, 0));
}

static int s_sba_threaded_reallocs(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(12);

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, true);

    s_thread_test(allocator, s_threaded_realloc_worker, sba);

    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_threaded_reallocs, s_sba_threaded_reallocs)

static int s_sba_churn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(9000);

    struct aws_array_list allocs;
    aws_array_list_init_dynamic(&allocs, allocator, NUM_TEST_ALLOCS, sizeof(void *));

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, false);

    size_t alloc_count = 0;
    while (alloc_count++ < NUM_TEST_ALLOCS * 10) {
        size_t size = aws_max_size(rand() % (2 * 4096), 1);
        void *alloc = aws_mem_acquire(sba, size);
        aws_array_list_push_back(&allocs, &alloc);

        /* randomly free a previous allocation, simulating the real world a bit */
        if ((rand() % allocs.length) > (allocs.length / 2)) {
            size_t idx = rand() % allocs.length;
            aws_array_list_get_at(&allocs, &alloc, idx);
            aws_array_list_erase(&allocs, idx);
            aws_mem_release(sba, alloc);
        }
    }

    /* free all remaining allocations */
    for (size_t idx = 0; idx < allocs.length; ++idx) {
        void *alloc = NULL;
        aws_array_list_get_at(&allocs, &alloc, idx);
        aws_mem_release(sba, alloc);
    }

    aws_array_list_clean_up(&allocs);

    aws_small_block_allocator_destroy(sba);

    return 0;
}
AWS_TEST_CASE(sba_churn, s_sba_churn)

static int s_sba_metrics_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_allocator *sba = aws_small_block_allocator_new(allocator, false);

    size_t expected_active_size = 0;
    void *allocs[512] = {0};
    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        size_t size = idx + 1;
        size_t bin_size = 0;
        ASSERT_SUCCESS(aws_round_up_to_power_of_two(size, &bin_size));
        expected_active_size += bin_size;
        allocs[idx] = aws_mem_acquire(sba, size);

        ASSERT_TRUE(aws_small_block_allocator_bytes_reserved(sba) > aws_small_block_allocator_bytes_active(sba));
        ASSERT_TRUE(expected_active_size <= aws_small_block_allocator_bytes_active(sba));
    }

    /*
     * There are
     *
     *   32 allocations of size < 32 # (bin 0)
     *   32 allocations of 32 < size <= 64 # (bin 1)
     *   64 allocations of 64 < size <= 128 # (bin 2)
     *   128 allocations of 128 < size <= 256 # (bin 3)
     *   256 allocations of 256 < size <= 512 # (bin 4)
     *
     * If we let actual_page_size = allocated_page_size - sizeof(page_header), then we expect to have reserved
     *
     *   (32 + actual_page_size / 32 - 1) / (actual_page_size / 32) # (bin 0)
     *   (32 + actual_page_size / 64 - 1) / (actual_page_size / 64) # (bin 1)
     *   (64 + actual_page_size / 128 - 1) / (actual_page_size / 128) # (bin 2)
     *   (128 + actual_page_size / 256 - 1) / (actual_page_size / 256) # (bin 3)
     *   (256 + actual_page_size / 512 - 1) / (actual_page_size / 512) # (bin 4)
     *
     *   total pages during the allocations.
     */
    size_t actual_page_size = aws_small_block_allocator_page_size_available(sba);

    size_t bin0_pages = (32 + actual_page_size / 32 - 1) / (actual_page_size / 32);
    size_t bin1_pages = (32 + actual_page_size / 64 - 1) / (actual_page_size / 64);
    size_t bin2_pages = (64 + actual_page_size / 128 - 1) / (actual_page_size / 128);
    size_t bin3_pages = (128 + actual_page_size / 256 - 1) / (actual_page_size / 256);
    size_t bin4_pages = (256 + actual_page_size / 512 - 1) / (actual_page_size / 512);
    size_t expected_page_count = bin0_pages + bin1_pages + bin2_pages + bin3_pages + bin4_pages;
    ASSERT_INT_EQUALS(
        expected_page_count * aws_small_block_allocator_page_size(sba), aws_small_block_allocator_bytes_reserved(sba));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        aws_mem_release(sba, allocs[idx]);
    }

    ASSERT_INT_EQUALS(0, aws_small_block_allocator_bytes_active(sba));

    /* after freeing everything, we should have relinquished all but one page in each bin */
    ASSERT_INT_EQUALS(5 * aws_small_block_allocator_page_size(sba), aws_small_block_allocator_bytes_reserved(sba));

    aws_small_block_allocator_destroy(sba);
    return 0;
}
AWS_TEST_CASE(sba_metrics, s_sba_metrics_test)

/*
 * Default allocator tests.
 */
static int s_default_threaded_reallocs(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(15);

    s_thread_test(allocator, s_threaded_realloc_worker, allocator);

    return 0;
}
AWS_TEST_CASE(default_threaded_reallocs, s_default_threaded_reallocs)

static int s_default_threaded_allocs_and_frees(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(99);

    s_thread_test(allocator, s_threaded_alloc_worker, allocator);

    return 0;
}
AWS_TEST_CASE(default_threaded_allocs_and_frees, s_default_threaded_allocs_and_frees)

/*
 * No align allocator tests.
 */
static int s_aligned_threaded_reallocs(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    srand(15);

    struct aws_allocator *alloc = aws_mem_tracer_new(aws_aligned_allocator(), NULL, AWS_MEMTRACE_STACKS, 8);

    s_thread_test(alloc, s_threaded_realloc_worker, alloc);

    aws_mem_tracer_destroy(alloc);

    return 0;
}
AWS_TEST_CASE(aligned_threaded_reallocs, s_aligned_threaded_reallocs)

static int s_aligned_threaded_allocs_and_frees(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    srand(99);

    struct aws_allocator *alloc = aws_mem_tracer_new(aws_aligned_allocator(), NULL, AWS_MEMTRACE_STACKS, 8);

    s_thread_test(alloc, s_threaded_alloc_worker, alloc);

    aws_mem_tracer_destroy(alloc);

    return 0;
}
AWS_TEST_CASE(aligned_threaded_allocs_and_frees, s_aligned_threaded_allocs_and_frees)
