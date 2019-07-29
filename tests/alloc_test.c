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

#include <aws/common/common.h>

#include <aws/common/assert.h>
#include <aws/testing/aws_test_harness.h>

#ifdef __MACH__
#    include <CoreFoundation/CoreFoundation.h>
#endif

static int assertion_violations = 0;

void assert_handler(const char *cond_str, const char *file, int line) {
    (void)cond_str;
    (void)file;
    (void)line;
    assertion_violations++;
}

static void *s_test_alloc_acquire(struct aws_allocator *allocator, size_t size) {
    (void)allocator;
    return (size > 0) ? malloc(size) : NULL;
}

static void s_test_alloc_release(struct aws_allocator *allocator, void *ptr) {
    (void)allocator;
    free(ptr);
}

static void *s_test_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    (void)allocator;
    (void)oldsize;
    /* Realloc should ensure that newsize is never 0 */
    AWS_FATAL_ASSERT(newsize != 0);
    return realloc(ptr, newsize);
}

static void *s_test_calloc(struct aws_allocator *allocator, size_t num, size_t size) {
    (void)allocator;
    return (num > 0 && size > 0) ? calloc(num, size) : NULL;
}

#define EXPECT_ASSERTION_VIOLATION(call)                                                                               \
    do {                                                                                                               \
        assertion_violations = 0;                                                                                      \
        call;                                                                                                          \
        ASSERT_TRUE(assertion_violations == 1);                                                                        \
    } while (0)

#define EXPECT_NO_ASSERTION_VIOLATION(call)                                                                            \
    do {                                                                                                               \
        assertion_violations = 0;                                                                                      \
        call;                                                                                                          \
        ASSERT_TRUE(assertion_violations == 0);                                                                        \
    } while (0)

/**
 * Check that we correctly protect against
 * https://wiki.sei.cmu.edu/confluence/display/c/MEM04-C.+Beware+of+zero-length+allocations
 */
AWS_TEST_CASE(test_alloc_nothing, s_test_alloc_nothing_fn)
static int s_test_alloc_nothing_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_allocator test_allocator = {.mem_acquire = s_test_alloc_acquire,
                                           .mem_release = s_test_alloc_release,
                                           .mem_realloc = s_test_realloc,
                                           .mem_calloc = s_test_calloc};
    assert_handler_fn_t old_assert_handler = register_assert_handler(assert_handler);
    /* mem_acquire and calloc fatal assert on 0 input */
    EXPECT_ASSERTION_VIOLATION(aws_mem_acquire(&test_allocator, 0));
    EXPECT_ASSERTION_VIOLATION(aws_mem_calloc(&test_allocator, 0, 12));
    EXPECT_ASSERTION_VIOLATION(aws_mem_calloc(&test_allocator, 12, 0));

    /* mem_release should handle null input */
    EXPECT_NO_ASSERTION_VIOLATION(aws_mem_release(&test_allocator, NULL));

    /* realloc should handle the case correctly and return null */
    assertion_violations = 0;
    void *p = aws_mem_acquire(&test_allocator, 12);
    ASSERT_SUCCESS(aws_mem_realloc(&test_allocator, &p, 12, 0));
    ASSERT_NULL(p);
    ASSERT_TRUE(assertion_violations == 0);
    register_assert_handler(old_assert_handler);
    return 0;
}
