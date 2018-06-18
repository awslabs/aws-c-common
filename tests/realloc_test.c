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
#include <aws/testing/aws_test_harness.h>

static size_t alloc_counter, alloc_total_size, call_ct_malloc, call_ct_free, call_ct_realloc;

static void *test_alloc_acquire(struct aws_allocator *allocator, size_t size) {
    alloc_counter++;
    call_ct_malloc++;
    alloc_total_size += size;

    uint8_t *buf = malloc(size + 16);
    *(size_t *)buf = size;
    buf += 16;
    return buf;
}

static void test_alloc_release(struct aws_allocator *allocator, void *ptr) {
    uint8_t *buf = ptr;
    call_ct_free++;

    buf -= 16;
    size_t old_size = *(size_t *)buf;
    alloc_counter--;
    alloc_total_size -= old_size;

    free(buf);
}

static size_t original_size, reported_oldsize;

static void *test_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    uint8_t *buf = ptr;
    buf -= 16;
    call_ct_realloc++;

    original_size = *(size_t *)buf;
    reported_oldsize = oldsize;

    /* Always pick a new pointer for test purposes */
    void *newbuf = malloc(newsize);
    if (!newbuf) abort();

    memcpy(newbuf, buf, 16 + (oldsize > newsize ? newsize : oldsize));
    free(buf);
    buf = newbuf;

    *(size_t *)buf = newsize;
    alloc_total_size += (newsize - oldsize);

    return buf + 16;
}

static void *test_malloc_failing(struct aws_allocator *allocator, size_t size) {
    return NULL;
}

static void *test_realloc_failing(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    return NULL;
}

static const uint8_t testpattern[32] = {
    0xa5, 0x41, 0xcb, 0xe7, 0x00, 0x19, 0xd9, 0xf3, 0x60, 0x4a, 0x2b, 0x68, 0x55, 0x46, 0xb7, 0xe0,
    0x74, 0x91, 0x2a, 0xbe, 0x5e, 0x41, 0x06, 0x39, 0x02, 0x02, 0xf6, 0x79, 0x1c, 0x4a, 0x08, 0xa9
};

AWS_TEST_CASE(test_realloc_fallback, test_realloc_fallback_fn)
static int test_realloc_fallback_fn(struct aws_allocator *unused, void *ctx) {
    struct aws_allocator allocator = {
        .mem_acquire = test_alloc_acquire,
        .mem_release = test_alloc_release,
        .mem_realloc = NULL
    };

    call_ct_malloc = call_ct_free = call_ct_realloc = 0;

    void *buf = aws_mem_acquire(&allocator, 32);
    void *oldbuf = buf;
    memcpy(buf, testpattern, 32);
    ASSERT_SUCCESS(aws_mem_realloc(&allocator, &buf, 32, 64));
    ASSERT_INT_EQUALS(call_ct_malloc, 2);
    ASSERT_INT_EQUALS(call_ct_free, 1);
    ASSERT_INT_EQUALS(alloc_counter, 1);
    ASSERT_INT_EQUALS(alloc_total_size, 64);
    ASSERT_INT_EQUALS(memcmp(buf, testpattern, 32), 0);
    ASSERT_FALSE(buf == oldbuf);

    aws_mem_release(&allocator, buf);

    return 0;
}

AWS_TEST_CASE(test_realloc_fallback_oom, test_realloc_fallback_oom_fn)
static int test_realloc_fallback_oom_fn(struct aws_allocator *unused, void *ctx) {
    struct aws_allocator allocator = {
        .mem_acquire = test_alloc_acquire,
        .mem_release = test_alloc_release,
        .mem_realloc = NULL
    };

    call_ct_malloc = call_ct_free = call_ct_realloc = 0;
    void *buf = aws_mem_acquire(&allocator, 32);
    void *oldbuf = buf;

    allocator.mem_acquire = test_malloc_failing;

    ASSERT_ERROR(AWS_ERROR_OOM, aws_mem_realloc(&allocator, &buf, 32, 64));
    ASSERT_INT_EQUALS(call_ct_free, 0);
    ASSERT_PTR_EQUALS(buf, oldbuf);

    aws_mem_release(&allocator, buf);

    return 0;
}

AWS_TEST_CASE(test_realloc_passthrough_oom, test_realloc_passthrough_oom_fn)
static int test_realloc_passthrough_oom_fn(struct aws_allocator *unused, void *ctx) {
    struct aws_allocator allocator = {
        .mem_acquire = test_alloc_acquire,
        .mem_release = test_alloc_release,
        .mem_realloc = test_realloc_failing
    };

    call_ct_malloc = call_ct_free = call_ct_realloc = 0;

    void *buf = aws_mem_acquire(&allocator, 32);
    void *oldbuf = buf;
    memcpy(buf, testpattern, 32);

    ASSERT_ERROR(AWS_ERROR_OOM, aws_mem_realloc(&allocator, &buf, 32, 64));
    ASSERT_PTR_EQUALS(buf, oldbuf);

    aws_mem_release(&allocator, buf);

    return 0;
}

AWS_TEST_CASE(test_realloc_passthrough, test_realloc_passthrough_fn)
static int test_realloc_passthrough_fn(struct aws_allocator *unused, void *ctx) {
    struct aws_allocator allocator = {
        .mem_acquire = test_alloc_acquire,
        .mem_release = test_alloc_release,
        .mem_realloc = test_realloc
    };

    call_ct_malloc = call_ct_free = call_ct_realloc = 0;

    void *buf = aws_mem_acquire(&allocator, 32);
    void *oldbuf = buf;
    memcpy(buf, testpattern, 32);

    ASSERT_SUCCESS(aws_mem_realloc(&allocator, &buf, 32, 64));
    ASSERT_INT_EQUALS(memcmp(buf, testpattern, 32), 0);
    ASSERT_INT_EQUALS(reported_oldsize, 32);
    ASSERT_INT_EQUALS(original_size, 32);
    ASSERT_INT_EQUALS(call_ct_malloc, 1);
    ASSERT_INT_EQUALS(call_ct_free, 0);
    ASSERT_FALSE(buf == oldbuf);

    aws_mem_release(&allocator, buf);

    return 0;
}
