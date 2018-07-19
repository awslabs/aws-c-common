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

#include <assert.h>

#include <aws/common/common.h>

struct aws_memory_pool {
    struct aws_allocator *alloc;
    size_t arena_size;
    size_t element_size;
    uint8_t *arena;
    void *free_list;
    int overflow_count;
};

struct aws_memory_pool *aws_memory_pool_init(struct aws_allocator* alloc, size_t element_size, int element_count) {
    size_t stride = element_size > sizeof(void *) ? element_size : sizeof(void *);
    size_t arena_size = sizeof(struct aws_memory_pool) + stride * element_count;
    struct aws_memory_pool *pool = (struct aws_memory_pool *)alloc->mem_acquire(alloc, arena_size);

    if (!pool) {
        aws_raise_error(AWS_ERROR_OOM);
        return NULL;
    }

    pool->alloc = alloc;
    pool->arena_size = arena_size;
    pool->element_size = element_size;
    pool->arena = (uint8_t *)(pool + 1);
    pool->free_list = pool->arena;
    pool->overflow_count = 0;

    /* Hook up singly linked list to represent the free list. */
    for (int i = 0; i < element_count - 1; ++i) {
        void **element_ptr = (void **)(pool->arena + stride * i);
        void *next = (void *)(pool->arena + stride * (i + 1));
        *element_ptr = next;
    };

    /* Last element points to NULL. */
    void **last_element_ptr = (void **)(pool->arena + stride * (element_count - 1));
    *last_element_ptr = NULL;

    return pool;
}

void aws_memory_pool_clean_up(struct aws_memory_pool *pool) {
    if (pool->overflow_count) {
        aws_raise_error(AWS_ERROR_MEMORY_LEAK);
        aws_mem_release(pool->alloc, pool);
        assert(0);
    } else {
        aws_mem_release(pool->alloc, pool);
    }
}

void *aws_memory_pool_try_acquire(struct aws_memory_pool *pool) {
    if (pool->free_list) {
        void *mem = pool->free_list;
        pool->free_list = *((void **)pool->free_list);
        return mem;
    } else {
        return NULL;
    }
}

void *aws_memory_pool_acquire(struct aws_memory_pool *pool) {
    void *mem = aws_memory_pool_try_acquire(pool);

    if (!mem) {
        mem = aws_mem_acquire(pool->alloc, pool->element_size);
        if (mem) {
            pool->overflow_count++;
        }
    }

    return mem;
}

void aws_memory_pool_release(struct aws_memory_pool *pool, void* to_release) {
    size_t difference = (size_t)((uint8_t *)to_release - (uint8_t *)(pool->arena));
    size_t in_bounds = difference < pool->arena_size;
    if (pool->overflow_count && !in_bounds) {
        aws_mem_release(pool->alloc, to_release);
        pool->overflow_count--;
    } else if (in_bounds) {
        *(void **)to_release = pool->free_list;
        pool->free_list = to_release;
    } else {
        /* Pointer was outside of arena bounds, or a double free was detected. */
        aws_raise_error(AWS_ERROR_BAD_FREE);
        assert(0);
    }
}
