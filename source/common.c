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

struct aws_allocator *aws_default_allocator() {
    return &default_allocator;
}

void *aws_mem_acquire(struct aws_allocator *allocator, size_t size) {
    void *mem = allocator->mem_acquire(allocator, size);
    if (!mem) {
        aws_raise_error(AWS_ERROR_OOM);
    }
    return mem;
}

#define AWS_ALIGN_ROUND_UP(value, alignment) (((value) + ((alignment)-1)) & -(alignment))

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
    return s_cf_allocator_description;
}

static CFIndex s_cf_allocator_preferred_size(CFIndex size, CFOptionFlags hint, void *info) {
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
        "success"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OOM,
        "out-of-memory"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_UNKNOWN,
        "unknown error"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_SHORT_BUFFER,
        "Insufficient data in input buffer"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_OVERFLOW_DETECTED,
        "fixed size value overflow was detected"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BUFFER_SIZE,
        "invalid buffer size"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_HEX_STR,
        "invalid hex string"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_BASE64_STR,
        "invalid base64 string"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_INVALID_INDEX,
        "invalid index for list access"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INVALID_SETTINGS,
        "invalid thread settings"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE,
        "thread, insufficient resources"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_PERMISSIONS,
        "insufficient permissions for thread operation"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NOT_JOINABLE,
        "thread not join-able"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_NO_SUCH_THREAD_ID,
        "no such thread id"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_THREAD_DEADLOCK_DETECTED,
        "deadlock detected"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_NOT_INIT,
        "mutex not initialized"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_TIMEOUT,
        "mutex operation timed out"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_CALLER_NOT_OWNER,
        "the caller of a mutex operation was not the owner"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_MUTEX_FAILED,
        "mutex operation failed"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_INIT_FAILED,
        "condition variable initialization failed."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_TIMED_OUT,
        "condition variable wait timed out."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN,
        "condition variable unknown error."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_CLOCK_FAILURE,
        "clock get ticks operation failed"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EMPTY,
        "empty list"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_DEST_COPY_TOO_SMALL,
        "destination of copy is too small"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_EXCEEDS_MAX_SIZE,
        "a requested operation on a list would exceed it's max size."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK,
        "attempt to shrink a list in static mode"),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_FULL,
        "attempt to add items to a full preallocated queue in static mode."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_PRIORITY_QUEUE_EMPTY,
        "attempt to pop an item from an empty queue."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_TASK_SCHEDULER_NO_TASKS,
        "no tasks scheduled available."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS,
        "none of the tasks scheduled is due to run now."),
    AWS_DEFINE_ERROR_INFO_COMMON(
        AWS_ERROR_HASHTBL_ITEM_NOT_FOUND,
        "Item not found in hash table"),
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
