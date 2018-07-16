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

#include <aws/common/memory_pool.h>

int aws_memory_pool_init(struct aws_memory_pool *pool, struct aws_allocator* alloc, size_t element_size, int element_count) {
    size_t stride = element_size + sizeof(void *);
    size_t arena_size = stride * element_count;
    pool->alloc = alloc;
    pool->element_size = element_size;
    pool->arena = alloc->mem_acquire(alloc, arena_size);
    pool->free_list = pool->arena;
    pool->overflow_count = 0;

    if (!pool->arena) {
        return AWS_OP_ERR;
    }

    /* Hook up singly linked list to represent the free list. */
    for (int i = 0; i < element_count - 1; ++i) {
        void **element_ptr = (void **)AWS_PTR_ADD(pool->arena, stride * i);
        void *next = AWS_PTR_ADD(pool->arena, stride * (i + 1));
        *element_ptr = next;
    };

    /* Last element points to NULL. */
    void **last_element_ptr = (void **)AWS_PTR_ADD(pool->arena, stride * (element_count - 1));
    last_element_ptr = NULL;

    return AWS_OP_SUCCESS;
}

void aws_memory_pool_clean_up(struct aws_memory_pool *pool) {
    aws_mem_release(pool->alloc, pool->arena);
}

void *aws_memory_pool_acquire(struct aws_memory_pool *pool) {
    if (pool->free_list) {
        void* mem = AWS_PTR_ADD(pool->free_list, sizeof(void *));
        pool->free_list = *((void **)pool->free_list);
        return mem;
    }

    void* mem = aws_mem_acquire(pool->alloc, pool->element_size);
    pool->overflow_count++;
    return mem;
}

void aws_memory_pool_release(struct aws_memory_pool *pool, void* to_release) {
    if (pool->overflow_count) {
        aws_mem_release(pool->alloc, to_release);
        pool->overflow_count--;
    } else {
        void** pool_element = (void **)AWS_PTR_SUB(to_release, sizeof(void *));
        *pool_element = pool->free_list;
        pool->free_list = pool_element;
    }
}
