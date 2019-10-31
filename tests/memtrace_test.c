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

#include <aws/testing/aws_test_harness.h>

#include <aws/common/allocator.h>
#include <aws/common/device_random.h>

#define NUM_ALLOCS 100
static int s_test_memtrace_count(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_allocator *tracer = aws_mem_tracer_new(allocator, AWS_MEMTRACE_BYTES, 0);

    void *allocs[NUM_ALLOCS] = {0};
    size_t sizes[NUM_ALLOCS] = {0};
    size_t total = 0;

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        uint32_t size = 0;
        aws_device_random_u32(&size);
        size = (size % 1024) + 1; /* not necessary to allocate a gajillion bytes */
        allocs[idx] = aws_mem_acquire(tracer, size);
        sizes[idx] = size;
        total += size;
    }

    ASSERT_UINT_EQUALS(total, aws_mem_tracer_count(tracer));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        uint32_t roll = 0;
        aws_device_random_u32(&roll);
        if (roll % 3 == 0) {
            aws_mem_release(tracer, allocs[idx]);
            allocs[idx] = NULL;
            total -= sizes[idx];
        }
    }

    ASSERT_UINT_EQUALS(total, aws_mem_tracer_count(tracer));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        if (allocs[idx]) {
            aws_mem_release(tracer, allocs[idx]);
        }
    }

    ASSERT_UINT_EQUALS(0, aws_mem_tracer_count(tracer));

    struct aws_allocator *original = aws_mem_tracer_destroy(tracer);
    ASSERT_PTR_EQUALS(allocator, original);

    return 0;
}
AWS_TEST_CASE(test_memtrace_count, s_test_memtrace_count)

static void *s_alloc_1(struct aws_allocator *allocator, size_t size) {
    return aws_mem_acquire(allocator, size);
}

static void *s_alloc_2(struct aws_allocator *allocator, size_t size) {
    return aws_mem_acquire(allocator, size);
}

static void *s_alloc_3(struct aws_allocator *allocator, size_t size) {
    return aws_mem_acquire(allocator, size);
}

static void *s_alloc_4(struct aws_allocator *allocator, size_t size) {
    return aws_mem_acquire(allocator, size);
}

static int s_test_memtrace_stacks(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_allocator *tracer = aws_mem_tracer_new(allocator, AWS_MEMTRACE_STACKS, 8);

    void *allocs[NUM_ALLOCS] = {0};
    size_t sizes[NUM_ALLOCS] = {0};
    size_t total = 0;

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        uint32_t size = 0;
        aws_device_random_u32(&size);
        size = (size % 1024) + 1; /* not necessary to allocate a gajillion bytes */

        void*(*allocate)(struct aws_allocator*, size_t) = NULL;
        switch (idx % 4) {
            case 0:
                allocate = s_alloc_1;
                break;
            case 1:
                allocate = s_alloc_2;
                break;
            case 2:
                allocate = s_alloc_3;
                break;
            case 3:
                allocate = s_alloc_4;
                break;
        }

        allocs[idx] = allocate(tracer, size);
        sizes[idx] = size;
        total += size;
    }

    ASSERT_UINT_EQUALS(total, aws_mem_tracer_count(tracer));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        uint32_t roll = 0;
        aws_device_random_u32(&roll);
        if (roll % 3 == 0) {
            aws_mem_release(tracer, allocs[idx]);
            allocs[idx] = NULL;
            total -= sizes[idx];
        }
    }

    ASSERT_UINT_EQUALS(total, aws_mem_tracer_count(tracer));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        if (allocs[idx]) {
            aws_mem_release(tracer, allocs[idx]);
        }
    }

    ASSERT_UINT_EQUALS(0, aws_mem_tracer_count(tracer));

    struct aws_allocator *original = aws_mem_tracer_destroy(tracer);
    ASSERT_PTR_EQUALS(allocator, original);

    return 0;
}
AWS_TEST_CASE(test_memtrace_stacks, s_test_memtrace_stacks)

static int s_test_memtrace_none(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_allocator *tracer = aws_mem_tracer_new(allocator, AWS_MEMTRACE_NONE, 0);

    void *allocs[NUM_ALLOCS] = {0};
    size_t sizes[NUM_ALLOCS] = {0};
    size_t total = 0;

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        uint32_t size = 0;
        aws_device_random_u32(&size);
        size = (size % 1024) + 1; /* not necessary to allocate a gajillion bytes */
        allocs[idx] = aws_mem_acquire(tracer, size);
        sizes[idx] = size;
        total += size;
    }

    ASSERT_UINT_EQUALS(0, aws_mem_tracer_count(tracer));

    for (int idx = 0; idx < AWS_ARRAY_SIZE(allocs); ++idx) {
        if (allocs[idx]) {
            aws_mem_release(tracer, allocs[idx]);
        }
    }

    ASSERT_UINT_EQUALS(0, aws_mem_tracer_count(tracer));

    struct aws_allocator *original = aws_mem_tracer_destroy(tracer);
    ASSERT_PTR_EQUALS(allocator, original);

    return 0;
}
AWS_TEST_CASE(test_memtrace_none, s_test_memtrace_none)

