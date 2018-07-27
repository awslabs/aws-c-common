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
#include <aws/testing/aws_test_harness.h>

#define AWS_MEMORY_POOL_TEST_ITERATIONS 10

AWS_TEST_CASE(test_memory_pool_no_overflow, test_memory_pool_no_overflow_fn)
static int test_memory_pool_no_overflow_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_memory_pool *pool = aws_memory_pool_init(allocator, sizeof(int), AWS_MEMORY_POOL_TEST_ITERATIONS);
    ASSERT_NOT_NULL(pool);

    int *ptrs[AWS_MEMORY_POOL_TEST_ITERATIONS];

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        void* mem = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem);
        int* val_ptr = (int*)mem;
        *val_ptr = i;
        ptrs[i] = val_ptr;
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        ASSERT_INT_EQUALS(i, *ptrs[i]);
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        aws_memory_pool_release(pool, ptrs[i]);
    }

    aws_memory_pool_clean_up(pool);

    return 0;
}

AWS_TEST_CASE(test_memory_pool_overflow, test_memory_pool_overflow_fn)
static int test_memory_pool_overflow_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_memory_pool *pool = aws_memory_pool_init(allocator, sizeof(int), AWS_MEMORY_POOL_TEST_ITERATIONS);
    ASSERT_NOT_NULL(pool);

    int *ptrs[AWS_MEMORY_POOL_TEST_ITERATIONS];

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        void* mem = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem);
        int* val_ptr = (int*)mem;
        *val_ptr = i;
        ptrs[i] = val_ptr;
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        ASSERT_INT_EQUALS(i, *ptrs[i]);
    }

    {
        void* mem0 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem0);
        void* mem1 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem1);
        void* mem2 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem2);
        aws_memory_pool_release(pool, mem0);
        aws_memory_pool_release(pool, mem1);
        aws_memory_pool_release(pool, mem2);
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        aws_memory_pool_release(pool, ptrs[i]);
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        void* mem = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem);
        int* val_ptr = (int*)mem;
        *val_ptr = i;
        ptrs[i] = val_ptr;
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        ASSERT_INT_EQUALS(i, *ptrs[i]);
    }

    {
        void* mem0 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem0);
        void* mem1 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem1);
        void* mem2 = aws_memory_pool_acquire(pool);
        ASSERT_NOT_NULL(mem2);
        aws_memory_pool_release(pool, mem0);
        aws_memory_pool_release(pool, mem1);
        aws_memory_pool_release(pool, mem2);
    }

    for (int i = 0; i < AWS_MEMORY_POOL_TEST_ITERATIONS; ++i) {
        aws_memory_pool_release(pool, ptrs[i]);
    }

    aws_memory_pool_clean_up(pool);

    return 0;
}

AWS_TEST_CASE(test_memory_pool_hammer, test_memory_pool_hammer_fn)
static int test_memory_pool_hammer_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_memory_pool *pool = aws_memory_pool_init(allocator, sizeof(int), 1);
    ASSERT_NOT_NULL(pool);

    void **ptrs = (void **)aws_mem_acquire(allocator, sizeof(void *) * 5 * 5);
    int index = 0;

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            ptrs[index++] = aws_memory_pool_acquire(pool);
        }
    }

    index = 0;

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            aws_memory_pool_release(pool, ptrs[index++]);
        }
    }

    index = 0;

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            ptrs[index++] = aws_memory_pool_acquire(pool);
        }
    }

    for (int i = 0; i < 5; ++i) {
        for (int j = 0; j < 5; ++j) {
            aws_memory_pool_release(pool, ptrs[--index]);
        }
    }

    aws_memory_pool_clean_up(pool);
    aws_mem_release(allocator, ptrs);

    return 0;
}
