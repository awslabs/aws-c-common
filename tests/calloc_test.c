/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>
#include <aws/common/math.h>
#include <aws/testing/aws_test_harness.h>
#include <stdlib.h>

static void *s_calloc_stub(struct aws_allocator *allocator, size_t num, size_t size) {
    allocator->impl = (void *)(num * size);
    return calloc(num, size);
}

static void s_mem_release_stub(struct aws_allocator *allocator, void *ptr) {
    allocator->impl = 0;
    free(ptr);
}

static int s_test_calloc_on_given_allocator(struct aws_allocator *allocator, bool using_calloc_stub_impl) {
    /* Check that calloc gives 0ed memory */
    char *p = aws_mem_calloc(allocator, 2, 4);
    ASSERT_NOT_NULL(p);
    for (size_t i = 0; i < 2 * 4; ++i) {
        ASSERT_TRUE(p[i] == 0);
    }
    if (using_calloc_stub_impl) {
        ASSERT_TRUE((intptr_t)allocator->impl == 8);
    }
    aws_mem_release(allocator, p);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_calloc_override, s_test_calloc_override_fn)
static int s_test_calloc_override_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    struct aws_allocator my_alloc = {
        .mem_calloc = s_calloc_stub,
        .mem_release = s_mem_release_stub,
    };
    return s_test_calloc_on_given_allocator(&my_alloc, true);
}

AWS_TEST_CASE(test_calloc_fallback_from_default_allocator, s_test_calloc_fallback_from_default_allocator_fn)
static int s_test_calloc_fallback_from_default_allocator_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_allocator my_alloc = *aws_default_allocator();
    my_alloc.mem_calloc = NULL;
    return s_test_calloc_on_given_allocator(&my_alloc, false);
}

AWS_TEST_CASE(test_calloc_fallback_from_given, s_test_calloc_fallback_from_given_fn)
static int s_test_calloc_fallback_from_given_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_allocator my_alloc = *allocator;
    my_alloc.mem_calloc = NULL;
    return s_test_calloc_on_given_allocator(&my_alloc, false);
}

AWS_TEST_CASE(test_calloc_from_default_allocator, s_test_calloc_from_default_allocator_fn)
static int s_test_calloc_from_default_allocator_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    return s_test_calloc_on_given_allocator(aws_default_allocator(), false);
}

AWS_TEST_CASE(test_calloc_from_given_allocator, s_test_calloc_from_given_allocator_fn)
static int s_test_calloc_from_given_allocator_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    return s_test_calloc_on_given_allocator(allocator, false);
}
