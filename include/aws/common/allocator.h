#ifndef AWS_COMMON_ALLOCATOR_H
#define AWS_COMMON_ALLOCATOR_H
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

#include <aws/common/macros.h>
#include <aws/common/stdbool.h>
#include <aws/common/stdint.h>

AWS_EXTERN_C_BEGIN

/* Allocator structure. An instance of this will be passed around for anything needing memory allocation */
struct aws_allocator {
    void *(*mem_acquire)(struct aws_allocator *allocator, size_t size);
    void (*mem_release)(struct aws_allocator *allocator, void *ptr);
    /* Optional method; if not supported, this pointer must be NULL */
    void *(*mem_realloc)(struct aws_allocator *allocator, void *oldptr, size_t oldsize, size_t newsize);
    /* Optional method; if not supported, this pointer must be NULL */
    void *(*mem_calloc)(struct aws_allocator *allocator, size_t num, size_t size);
    void *impl;
};

/**
 * Inexpensive (constant time) check of data-structure invariants.
 */
AWS_COMMON_API
bool aws_allocator_is_valid(const struct aws_allocator *alloc);

AWS_COMMON_API
struct aws_allocator *aws_default_allocator(void);

#ifdef __MACH__
/* Avoid pulling in CoreFoundation headers in a header file. */
struct __CFAllocator;
typedef const struct __CFAllocator *CFAllocatorRef;

/**
 * Wraps a CFAllocator around aws_allocator. For Mac only. Use this anytime you need a CFAllocatorRef for interacting
 * with Apple Frameworks. Unfortunately, it allocates memory so we can't make it static file scope, be sure to call
 * aws_wrapped_cf_allocator_destroy when finished.
 */
AWS_COMMON_API
CFAllocatorRef aws_wrapped_cf_allocator_new(struct aws_allocator *allocator);

/**
 * Cleans up any resources alloced in aws_wrapped_cf_allocator_new.
 */
AWS_COMMON_API
void aws_wrapped_cf_allocator_destroy(CFAllocatorRef allocator);
#endif

/**
 * Returns at least `size` of memory ready for usage or returns NULL on failure.
 */
AWS_COMMON_API
void *aws_mem_acquire(struct aws_allocator *allocator, size_t size);

/**
 * Allocates a block of memory for an array of num elements, each of them size bytes long, and initializes all its bits
 * to zero. Returns null on failure.
 */
AWS_COMMON_API
void *aws_mem_calloc(struct aws_allocator *allocator, size_t num, size_t size);

/**
 * Allocates many chunks of bytes into a single block. Expects to be called with alternating void ** (dest), size_t
 * (size). The first void ** will be set to the root of the allocation. Alignment is assumed to be sizeof(intmax_t).
 *
 * This is useful for allocating structs using the pimpl pattern, as you may allocate the public object and impl object
 * in the same contiguous block of memory.
 *
 * Returns a pointer to the allocation.
 */
AWS_COMMON_API
void *aws_mem_acquire_many(struct aws_allocator *allocator, size_t count, ...);

/**
 * Releases ptr back to whatever allocated it.
 */
AWS_COMMON_API
void aws_mem_release(struct aws_allocator *allocator, void *ptr);

/*
 * Attempts to adjust the size of the pointed-to memory buffer from oldsize to
 * newsize. The pointer (*ptr) may be changed if the memory needs to be
 * reallocated.
 *
 * If reallocation fails, *ptr is unchanged, and this method raises an
 * AWS_ERROR_OOM error.
 */
AWS_COMMON_API
int aws_mem_realloc(struct aws_allocator *allocator, void **ptr, size_t oldsize, size_t newsize);
/*
 * Maintainer note: The above function doesn't return the pointer (as with
 * standard C realloc) as this pattern becomes error-prone when OOMs occur.
 * In particular, we want to avoid losing the old pointer when an OOM condition
 * occurs, so we prefer to take the old pointer as an in/out reference argument
 * that we can leave unchanged on failure.
 */

AWS_EXTERN_C_END

#endif /* AWS_COMMON_ALLOCATOR_H */
