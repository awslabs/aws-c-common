#ifndef AWS_IO_MEMORY_POOL_H
#define AWS_IO_MEMORY_POOL_H
/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

struct aws_memory_pool;

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Constructs a memory pool where internal elements are all of the size `element_size`. Internally a single memory arena
 * is created.
 */
AWS_COMMON_API struct aws_memory_pool *aws_memory_pool_init(
    struct aws_allocator *alloc,
    size_t element_size,
    int element_count);

/**
 * Releases the all resources associated with `pool`. Does not release any "overflow" allocations (see \ref
 * aws_memory_pool_acquire).
 */
AWS_COMMON_API void aws_memory_pool_clean_up(struct aws_memory_pool *pool);

/**
 * Acquires memory from the pool. If no more memory in the pool is available an "overflow" allocation is made via
 * `alloc`, and returned.
 */
AWS_COMMON_API void *aws_memory_pool_acquire(struct aws_memory_pool *pool);

/**
 * Acquires memory from the pool. If the pool is full returns NULL.
 */
AWS_COMMON_API void *aws_memory_pool_try_acquire(struct aws_memory_pool *pool);

/**
 * Release memory at `to_release`. Releases the memory to the pool or via `alloc->mem_release` depending on if
 * `to_release` was allocated from the internal arena, or from a "one-shot" allocation (happens when the arena is
 * completely full).
 */
AWS_COMMON_API void aws_memory_pool_release(struct aws_memory_pool *pool, void *to_release);

/**
 * Returns the internal memory arena and its size in the pointers `arena` and `arena_size` respectively.
 */
AWS_COMMON_API void aws_memory_pool_get_arena(struct aws_memory_pool *pool, void **arena, size_t *arena_size);

#ifdef __cplusplus
}
#endif

#endif /* AWS_IO_MEMORY_POOL_H */
