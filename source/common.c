/*
 * Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/common.h>

#include <stdarg.h>
#include <stdlib.h>

#ifdef _WIN32
#    include <Windows.h>
#endif

#ifdef __MACH__
#    include <CoreFoundation/CoreFoundation.h>
#endif

/* turn off unused named parameter warning on msvc.*/
#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4100)
#endif

static void *s_default_malloc(struct aws_allocator *allocator, size_t size) {
    (void)allocator;
    return malloc(size);
}

static void s_default_free(struct aws_allocator *allocator, void *ptr) {
    (void)allocator;
    free(ptr);
}

static void *s_default_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    (void)allocator;
    (void)oldsize;
    return realloc(ptr, newsize);
}

static struct aws_allocator default_allocator = {
    .mem_acquire = s_default_malloc,
    .mem_release = s_default_free,
    .mem_realloc = s_default_realloc,
};

struct aws_allocator *aws_default_allocator(void) {
    return &default_allocator;
}

void *aws_mem_acquire(struct aws_allocator *allocator, size_t size) {
    void *mem = allocator->mem_acquire(allocator, size);
    if (!mem) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    return mem;
}

#define AWS_ALIGN_ROUND_UP(value, alignment) (((value) + ((alignment)-1)) & ~((alignment)-1))

void *aws_mem_acquire_many(struct aws_allocator *allocator, size_t count, ...) {

    enum { S_ALIGNMENT = sizeof(intmax_t) };

    va_list args_size;
    va_start(args_size, count);
    va_list args_allocs;
    va_copy(args_allocs, args_size);

    size_t total_size = 0;
    for (size_t i = 0; i < count; ++i) {

        /* Ignore the pointer argument for now */
        va_arg(args_size, void **);

        size_t alloc_size = va_arg(args_size, size_t);
        total_size += AWS_ALIGN_ROUND_UP(alloc_size, S_ALIGNMENT);
    }
    va_end(args_size);

    void *allocation = NULL;

    if (total_size > 0) {

        allocation = aws_mem_acquire(allocator, total_size);
        if (!allocation) {
            goto cleanup;
        }

        uint8_t *current_ptr = allocation;

        for (size_t i = 0; i < count; ++i) {

            void **out_ptr = va_arg(args_allocs, void **);

            size_t alloc_size = va_arg(args_allocs, size_t);
            alloc_size = AWS_ALIGN_ROUND_UP(alloc_size, S_ALIGNMENT);

            *out_ptr = current_ptr;
            current_ptr += alloc_size;
        }
    }

cleanup:
    va_end(args_allocs);
    return allocation;
}

#undef AWS_ALIGN_ROUND_UP

void aws_mem_release(struct aws_allocator *allocator, void *ptr) {
    allocator->mem_release(allocator, ptr);
}

int aws_mem_realloc(struct aws_allocator *allocator, void **ptr, size_t oldsize, size_t newsize) {
    if (allocator->mem_realloc) {
        void *newptr = allocator->mem_realloc(allocator, *ptr, oldsize, newsize);
        if (!newptr) {
            return aws_raise_error(AWS_ERROR_OOM);
        }
        *ptr = newptr;
        return AWS_OP_SUCCESS;
    }

    /* Since the allocator doesn't support realloc, we'll need to emulate it
     * (inefficiently). */
    if (oldsize >= newsize) {
        return AWS_OP_SUCCESS;
    }

    void *newptr = aws_mem_acquire(allocator, newsize);
    if (!newptr) {
        /* AWS_ERROR_OOM already raised */
        return AWS_OP_ERR;
    }

    memcpy(newptr, *ptr, oldsize);
    memset((uint8_t *)newptr + oldsize, 0, newsize - oldsize);

    aws_mem_release(allocator, *ptr);

    *ptr = newptr;

    return AWS_OP_SUCCESS;
}

/* Wraps a CFAllocator around aws_allocator. For Mac only. */
#ifdef __MACH__

static CFStringRef s_cf_allocator_description = CFSTR("CFAllocator wrapping aws_allocator.");

/* note we don't have a standard specification stating sizeof(size_t) == sizeof(void *) so we have some extra casts */
static void *s_cf_allocator_allocate(CFIndex alloc_size, CFOptionFlags hint, void *info) {
    (void)hint;

    struct aws_allocator *allocator = info;

    void *mem = aws_mem_acquire(allocator, (size_t)alloc_size + sizeof(size_t));

    if (!mem) {
        return NULL;
    }

    size_t allocation_size = (size_t)alloc_size + sizeof(size_t);
    memcpy(mem, &allocation_size, sizeof(size_t));
    return (void *)((uint8_t *)mem + sizeof(size_t));
}

static void s_cf_allocator_deallocate(void *ptr, void *info) {
    struct aws_allocator *allocator = info;

    void *original_allocation = (uint8_t *)ptr - sizeof(size_t);

    aws_mem_release(allocator, original_allocation);
}

static void *s_cf_allocator_reallocate(void *ptr, CFIndex new_size, CFOptionFlags hint, void *info) {
    (void)hint;

    struct aws_allocator *allocator = info;
    assert(allocator->mem_realloc);

    void *original_allocation = (uint8_t *)ptr - sizeof(size_t);
    size_t original_size = 0;
    memcpy(&original_size, original_allocation, sizeof(size_t));

    if (aws_mem_realloc(allocator, &original_allocation, original_size, (size_t)new_size)) {
        return NULL;
    }

    size_t new_allocation_size = (size_t)new_size;
    memcpy(original_allocation, &new_allocation_size, sizeof(size_t));

    return (void *)((uint8_t *)original_allocation + sizeof(size_t));
}

static CFStringRef s_cf_allocator_copy_description(const void *info) {
    (void)info;

    return s_cf_allocator_description;
}

static CFIndex s_cf_allocator_preferred_size(CFIndex size, CFOptionFlags hint, void *info) {
    (void)hint;
    (void)info;

    return size + sizeof(size_t);
}

CFAllocatorRef aws_wrapped_cf_allocator_new(struct aws_allocator *allocator) {
    CFAllocatorRef cf_allocator = NULL;

    CFAllocatorReallocateCallBack reallocate_callback = NULL;

    if (allocator->mem_realloc) {
        reallocate_callback = s_cf_allocator_reallocate;
    }

    CFAllocatorContext context = {
        .allocate = s_cf_allocator_allocate,
        .copyDescription = s_cf_allocator_copy_description,
        .deallocate = s_cf_allocator_deallocate,
        .reallocate = reallocate_callback,
        .info = allocator,
        .preferredSize = s_cf_allocator_preferred_size,
        .release = NULL,
        .retain = NULL,
        .version = 0,
    };

    cf_allocator = CFAllocatorCreate(NULL, &context);

    if (!cf_allocator) {
        aws_raise_error(AWS_ERROR_OOM);
    }

    return cf_allocator;
}

void aws_wrapped_cf_allocator_destroy(CFAllocatorRef allocator) {
    CFRelease(allocator);
}

#endif /*__MACH__ */

static int8_t s_error_strings_loaded = 0;

#define AWS_DEFINE_ERROR_INFO_COMMON(C, ES) AWS_DEFINE_ERROR_INFO(C, ES, "libaws-c-common")

/* clang-format off */
static struct aws_error_info errors[] = {
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SUCCESS,
        "Success."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OOM,
        "Out of memory."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNKNOWN,
        "Unknown error."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SHORT_BUFFER,
        "Buffer is not large enough to hold result."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OVERFLOW_DETECTED,
        "Fixed size value overflow was detected."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNSUPPORTED_OPERATION,
        "Unsupported operation."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BUFFER_SIZE,
        "Invalid buffer size."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_HEX_STR,
        "Invalid hex string."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BASE64_STR,
        "Invalid base64 string."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_INDEX,
        "Invalid index for list access."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INVALID_SETTINGS,
        "Invalid thread settings."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE,
        "Insufficent resources for thread."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_PERMISSIONS,
        "Insufficient permissions for thread operation."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NOT_JOINABLE,
        "Thread not joinable."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_SUCH_THREAD_ID,
        "No such thread ID."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_DEADLOCK_DETECTED,
        "Deadlock detected in thread."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_NOT_INIT,
        "Mutex not initialized."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_TIMEOUT,
        "Mutex operation timed out."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_CALLER_NOT_OWNER,
        "The caller of a mutex operation was not the owner."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_FAILED,
        "Mutex operation failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_INIT_FAILED,
        "Condition variable initialization failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_TIMED_OUT,
        "Condition variable wait timed out."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN,
        "Condition variable unknown error."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_CLOCK_FAILURE,
        "Clock operation failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EMPTY,
        "Empty list."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_DEST_COPY_TOO_SMALL,
        "Destination of copy is too small."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EXCEEDS_MAX_SIZE,
        "A requested operation on a list would exceed it's max size."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK,
        "Attempt to shrink a list in static mode."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_FULL,
        "Attempt to add items to a full preallocated queue in static mode."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_EMPTY,
        "Attempt to pop an item from an empty queue."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_BAD_NODE,
        "Bad node handle passed to remove."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_HASHTBL_ITEM_NOT_FOUND,
        "Item not found in hash table."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_DATE_STR,
        "Date string is invalid and cannot be parsed."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_ARGUMENT,
        "An invalid argument was passed to a function."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_RANDOM_GEN_FAILED,
        "A call to the random number generator failed. Retry later."
    ),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MALFORMED_INPUT_STRING,
        "An input string was passed to a parser and the string was incorrectly formatted."
    ),
};
/* clang-format on */

static struct aws_error_info_list s_list = {
    .error_list = errors,
    .count = AWS_ARRAY_SIZE(errors),
};

void aws_load_error_strings(void) {
    if (!s_error_strings_loaded) {
        s_error_strings_loaded = 1;
        aws_register_error_info(&s_list);
    }
}

void aws_secure_zero(void *pBuf, size_t bufsize) {
#if defined(_WIN32)
    SecureZeroMemory(pBuf, bufsize);
#else
    /* We cannot use memset_s, even on a C11 compiler, because that would require
     * that __STDC_WANT_LIB_EXT1__ be defined before the _first_ inclusion of string.h.
     *
     * We'll try to work around this by using inline asm on GCC-like compilers,
     * and by exposing the buffer pointer in a volatile local pointer elsewhere.
     */
#    if defined(__GNUC__) || defined(__clang__)
    memset(pBuf, 0, bufsize);
    /* This inline asm serves to convince the compiler that the buffer is (somehow) still
     * used after the zero, and therefore that the optimizer can't eliminate the memset.
     */
    __asm__ __volatile__("" /* The asm doesn't actually do anything. */
                         :  /* no outputs */
                         /* Tell the compiler that the asm code has access to the pointer to the buffer,
                          * and therefore it might be reading the (now-zeroed) buffer.
                          * Without this. clang/LLVM 9.0.0 optimizes away a memset of a stack buffer.
                          */
                         : "r"(pBuf)
                         /* Also clobber memory. While this seems like it might be unnecessary - after all,
                          * it's enough that the asm might read the buffer, right? - in practice GCC 7.3.0
                          * seems to optimize a zero of a stack buffer without it.
                          */
                         : "memory");
#    else  // not GCC/clang
    /* We don't have access to inline asm, since we're on a non-GCC platform. Move the pointer
     * through a volatile pointer in an attempt to confuse the optimizer.
     */
    volatile void *pVolBuf = pBuf;
    memset(pVolBuf, 0, bufsize);
#    endif // #else not GCC/clang
#endif     // #else not windows
}

#ifdef _MSC_VER
#    pragma warning(pop)
#endif
