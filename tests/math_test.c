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

#include <aws/common/math.h>

#include <aws/testing/aws_test_harness.h>

#include <stdio.h>

#define CHECK_SAT(fn, a, b, result)                                                                                    \
    do {                                                                                                               \
        ASSERT_UINT_EQUALS(                                                                                            \
            (result),                                                                                                  \
            fn((a), (b)),                                                                                              \
            "%s(0x%016llx, 0x%016llx) = 0x%016llx",                                                                    \
            #fn,                                                                                                       \
            (unsigned long long)(a),                                                                                   \
            (unsigned long long)(b),                                                                                   \
            (unsigned long long)(result));                                                                             \
        ASSERT_UINT_EQUALS(                                                                                            \
            (result),                                                                                                  \
            fn((b), (a)),                                                                                              \
            "%s(0x%016llx, 0x%016llx) = 0x%016llx",                                                                    \
            #fn,                                                                                                       \
            (unsigned long long)(b),                                                                                   \
            (unsigned long long)(a),                                                                                   \
            (unsigned long long)(result));                                                                             \
    } while (0)

AWS_TEST_CASE(test_mul_u64_saturating, s_test_mul_u64_saturating_fn)
static int s_test_mul_u64_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    CHECK_SAT(aws_mul_u64_saturating, 0, 0, 0);
    CHECK_SAT(aws_mul_u64_saturating, 0, 1, 0);
    CHECK_SAT(aws_mul_u64_saturating, 0, ~0LLU, 0);
    CHECK_SAT(aws_mul_u64_saturating, 4, 5, 20);
    CHECK_SAT(aws_mul_u64_saturating, 1234, 4321, 5332114);

    CHECK_SAT(aws_mul_u64_saturating, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_SAT(aws_mul_u64_saturating, 0xFFFFFFFF, 0xFFFFFFFF, 0xfffffffe00000001LLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x100000000, 0xFFFFFFFF, 0xFFFFFFFF00000000LLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x100000001, 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x100000001, 0xFFFFFFFE, 0xFFFFFFFEFFFFFFFELLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x100000002, 0xFFFFFFFE, 0xFFFFFFFFFFFFFFFCLLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x100000003, 0xFFFFFFFE, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_u64_saturating, 0xFFFFFFFE, 0xFFFFFFFE, 0xFFFFFFFC00000004LLU);
    CHECK_SAT(aws_mul_u64_saturating, 0x1FFFFFFFF, 0x1FFFFFFFF, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_u64_saturating, ~0LLU, ~0LLU, ~0LLU);

    return 0;
}

AWS_TEST_CASE(test_mul_u32_saturating, s_test_mul_u32_saturating_fn)
static int s_test_mul_u32_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    CHECK_SAT(aws_mul_u32_saturating, 0, 0, 0);
    CHECK_SAT(aws_mul_u32_saturating, 0, 1, 0);
    CHECK_SAT(aws_mul_u32_saturating, 0, ~0U, 0);
    CHECK_SAT(aws_mul_u32_saturating, 4, 5, 20);
    CHECK_SAT(aws_mul_u32_saturating, 1234, 4321, 5332114);

    CHECK_SAT(aws_mul_u32_saturating, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_SAT(aws_mul_u32_saturating, 0xFFFF, 1, 0xFFFF);
    CHECK_SAT(aws_mul_u32_saturating, 0xFFFF, 0xFFFF, 0xfffe0001);
    CHECK_SAT(aws_mul_u32_saturating, 0x10000, 0xFFFF, 0xFFFF0000U);
    CHECK_SAT(aws_mul_u32_saturating, 0x10001, 0xFFFF, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_u32_saturating, 0x10001, 0xFFFE, 0xFFFEFFFEU);
    CHECK_SAT(aws_mul_u32_saturating, 0x10002, 0xFFFE, 0xFFFFFFFCU);
    CHECK_SAT(aws_mul_u32_saturating, 0x10003, 0xFFFE, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_u32_saturating, 0xFFFE, 0xFFFE, 0xFFFC0004U);
    CHECK_SAT(aws_mul_u32_saturating, 0x1FFFF, 0x1FFFF, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_u32_saturating, ~0U, ~0U, ~0U);

    return 0;
}

AWS_TEST_CASE(test_mul_size_saturating, s_test_mul_size_saturating_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_mul_size_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

#if SIZE_MAX == UINT32_MAX
    CHECK_SAT(aws_mul_size_saturating, 0, 0, 0);
    CHECK_SAT(aws_mul_size_saturating, 0, 1, 0);
    CHECK_SAT(aws_mul_size_saturating, 0, ~0U, 0);
    CHECK_SAT(aws_mul_size_saturating, 4, 5, 20);
    CHECK_SAT(aws_mul_size_saturating, 1234, 4321, 5332114);

    CHECK_SAT(aws_mul_size_saturating, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_SAT(aws_mul_size_saturating, 0xFFFF, 1, 0xFFFF);
    CHECK_SAT(aws_mul_size_saturating, 0xFFFF, 0xFFFF, 0xfffe0001);
    CHECK_SAT(aws_mul_size_saturating, 0x10000, 0xFFFF, 0xFFFF0000U);
    CHECK_SAT(aws_mul_size_saturating, 0x10001, 0xFFFF, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_size_saturating, 0x10001, 0xFFFE, 0xFFFEFFFEU);
    CHECK_SAT(aws_mul_size_saturating, 0x10002, 0xFFFE, 0xFFFFFFFCU);
    CHECK_SAT(aws_mul_size_saturating, 0x10003, 0xFFFE, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_size_saturating, 0xFFFE, 0xFFFE, 0xFFFC0004U);
    CHECK_SAT(aws_mul_size_saturating, 0x1FFFF, 0x1FFFF, 0xFFFFFFFFU);
    CHECK_SAT(aws_mul_size_saturating, ~0U, ~0U, ~0U);
#elif SIZE_MAX == UINT64_MAX
    CHECK_SAT(aws_mul_size_saturating, 0, 0, 0);
    CHECK_SAT(aws_mul_size_saturating, 0, 1, 0);
    CHECK_SAT(aws_mul_size_saturating, 0, ~0LLU, 0);
    CHECK_SAT(aws_mul_size_saturating, 4, 5, 20);
    CHECK_SAT(aws_mul_size_saturating, 1234, 4321, 5332114);

    CHECK_SAT(aws_mul_size_saturating, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_SAT(aws_mul_size_saturating, 0xFFFFFFFF, 0xFFFFFFFF, 0xfffffffe00000001LLU);
    CHECK_SAT(aws_mul_size_saturating, 0x100000000, 0xFFFFFFFF, 0xFFFFFFFF00000000LLU);
    CHECK_SAT(aws_mul_size_saturating, 0x100000001, 0xFFFFFFFF, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_size_saturating, 0x100000001, 0xFFFFFFFE, 0xFFFFFFFEFFFFFFFELLU);
    CHECK_SAT(aws_mul_size_saturating, 0x100000002, 0xFFFFFFFE, 0xFFFFFFFFFFFFFFFCLLU);
    CHECK_SAT(aws_mul_size_saturating, 0x100000003, 0xFFFFFFFE, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_size_saturating, 0xFFFFFFFE, 0xFFFFFFFE, 0xFFFFFFFC00000004LLU);
    CHECK_SAT(aws_mul_size_saturating, 0x1FFFFFFFF, 0x1FFFFFFFF, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_SAT(aws_mul_size_saturating, ~0LLU, ~0LLU, ~0LLU);
#else
    FAIL("Unexpected size for size_t: %zu", sizeof(size_t));
#endif

    return 0;
}

#define CHECK_OVF_0(fn, type, a, b)                                                                                    \
    do {                                                                                                               \
        type result_val;                                                                                               \
        ASSERT_TRUE(fn((a), (b), &result_val));                                                                        \
    } while (0)

#define CHECK_OVF(fn, type, a, b)                                                                                      \
    do {                                                                                                               \
        CHECK_OVF_0(fn, type, a, b);                                                                                   \
        CHECK_OVF_0(fn, type, b, a);                                                                                   \
    } while (0)

#define CHECK_NO_OVF_0(fn, type, a, b, r)                                                                              \
    do {                                                                                                               \
        type result_val;                                                                                               \
        ASSERT_FALSE(fn((a), (b), &result_val));                                                                       \
        ASSERT_INT_EQUALS(                                                                                             \
            (uint64_t)result_val,                                                                                      \
            (uint64_t)(r),                                                                                             \
            "Expected %s(%016llx, %016llx) = %016llx; got %016llx",                                                    \
            #fn,                                                                                                       \
            (unsigned long long)(a),                                                                                   \
            (unsigned long long)(b),                                                                                   \
            (unsigned long long)(r),                                                                                   \
            (unsigned long long)(result_val));                                                                         \
    } while (0)

#define CHECK_NO_OVF(fn, type, a, b, r)                                                                                \
    do {                                                                                                               \
        CHECK_NO_OVF_0(fn, type, a, b, r);                                                                             \
        CHECK_NO_OVF_0(fn, type, b, a, r);                                                                             \
    } while (0)

AWS_TEST_CASE(test_mul_u64_checked, s_test_mul_u64_checked_fn)
static int s_test_mul_u64_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0, 0, 0);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0, 1, 0);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0, ~0LLU, 0);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 4, 5, 20);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 1234, 4321, 5332114);

    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0xFFFFFFFFLLU, 1LLU, 0xFFFFFFFFLLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0xFFFFFFFFLLU, 0xFFFFFFFFLLU, 0xfffffffe00000001LLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0x100000000LLU, 0xFFFFFFFFLLU, 0xFFFFFFFF00000000LLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0x100000001LLU, 0xFFFFFFFFLLU, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0x100000001LLU, 0xFFFFFFFELLU, 0xFFFFFFFEFFFFFFFELLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0x100000002LLU, 0xFFFFFFFELLU, 0xFFFFFFFFFFFFFFFCLLU);
    CHECK_OVF(aws_mul_u64_checked, uint64_t, 0x100000003LLU, 0xFFFFFFFELLU);
    CHECK_NO_OVF(aws_mul_u64_checked, uint64_t, 0xFFFFFFFELLU, 0xFFFFFFFELLU, 0xFFFFFFFC00000004LLU);
    CHECK_OVF(aws_mul_u64_checked, uint64_t, 0x1FFFFFFFFLLU, 0x1FFFFFFFFLLU);
    CHECK_OVF(aws_mul_u64_checked, uint64_t, ~0LLU, ~0LLU);

    return 0;
}

AWS_TEST_CASE(test_mul_u32_checked, s_test_mul_u32_checked_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_mul_u32_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0, 0, 0);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0, 1, 0);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0, ~0u, 0);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 4, 5, 20);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 1234, 4321, 5332114);

    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0xFFFF, 1, 0xFFFF);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0xFFFF, 0xFFFF, 0xfffe0001u);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0x10000, 0xFFFF, 0xFFFF0000u);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0x10001, 0xFFFF, 0xFFFFFFFFu);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0x10001, 0xFFFE, 0xFFFEFFFEu);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0x10002, 0xFFFE, 0xFFFFFFFCu);
    CHECK_OVF(aws_mul_u32_checked, uint32_t, 0x10003, 0xFFFE);
    CHECK_NO_OVF(aws_mul_u32_checked, uint32_t, 0xFFFE, 0xFFFE, 0xFFFC0004u);
    CHECK_OVF(aws_mul_u32_checked, uint32_t, 0x1FFFF, 0x1FFFF);
    CHECK_OVF(aws_mul_u32_checked, uint32_t, ~0u, ~0u);

    return 0;
}

AWS_TEST_CASE(test_mul_size_checked, s_test_mul_size_checked_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_mul_size_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

#if SIZE_MAX == UINT32_MAX
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, 0, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, 1, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, ~0u, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 4, 5, 20);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 1234, 4321, 5332114);

    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFFFFFF, 1, 0xFFFFFFFF);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFF, 1, 0xFFFF);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFF, 0xFFFF, 0xfffe0001u);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x10000, 0xFFFF, 0xFFFF0000u);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x10001, 0xFFFF, 0xFFFFFFFFu);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x10001, 0xFFFE, 0xFFFEFFFEu);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x10002, 0xFFFE, 0xFFFFFFFCu);
    CHECK_OVF(aws_mul_size_checked, size_t, 0x10003, 0xFFFE);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFE, 0xFFFE, 0xFFFC0004u);
    CHECK_OVF(aws_mul_size_checked, size_t, 0x1FFFF, 0x1FFFF);
    CHECK_OVF(aws_mul_size_checked, size_t, ~0u, ~0u);
#elif SIZE_MAX == UINT64_MAX
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, 0, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, 1, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0, ~0LLU, 0);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 4, 5, 20);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 1234, 4321, 5332114);

    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFFFFFFLLU, 1LLU, 0xFFFFFFFFLLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFFFFFFLLU, 0xFFFFFFFFLLU, 0xfffffffe00000001LLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x100000000LLU, 0xFFFFFFFFLLU, 0xFFFFFFFF00000000LLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x100000001LLU, 0xFFFFFFFFLLU, 0xFFFFFFFFFFFFFFFFLLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x100000001LLU, 0xFFFFFFFELLU, 0xFFFFFFFEFFFFFFFELLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0x100000002LLU, 0xFFFFFFFELLU, 0xFFFFFFFFFFFFFFFCLLU);
    CHECK_OVF(aws_mul_size_checked, size_t, 0x100000003LLU, 0xFFFFFFFELLU);
    CHECK_NO_OVF(aws_mul_size_checked, size_t, 0xFFFFFFFELLU, 0xFFFFFFFELLU, 0xFFFFFFFC00000004LLU);
    CHECK_OVF(aws_mul_size_checked, size_t, 0x1FFFFFFFFLLU, 0x1FFFFFFFFLLU);
    CHECK_OVF(aws_mul_size_checked, size_t, ~0LLU, ~0LLU);
#else
    FAIL("Unexpected size for size_t: %zu", sizeof(size_t));
#endif
    return 0;
}

AWS_TEST_CASE(test_add_size_checked, s_test_add_size_checked_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_size_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

#if SIZE_MAX == UINT32_MAX
    const uint32_t HALF_MAX = UINT32_MAX / 2;
    const uint32_t ACTUAL_MAX = UINT32_MAX;
#elif SIZE_MAX == UINT64_MAX
    const uint64_t HALF_MAX = UINT64_MAX / 2;
    const uint64_t ACTUAL_MAX = UINT64_MAX;
#else
    FAIL("Unexpected size for size_t: %zu", sizeof(size_t));
#endif

    CHECK_NO_OVF(aws_add_size_checked, size_t, 0, 0, 0);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 0, 1, 1);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 4, 5, 9);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 1234, 4321, 5555);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_size_checked, size_t, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_NO_OVF(aws_add_size_checked, size_t, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_NO_OVF(aws_add_size_checked, size_t, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    CHECK_OVF(aws_add_size_checked, size_t, 1, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, 100, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, HALF_MAX + 1, HALF_MAX + 1);
    CHECK_OVF(aws_add_size_checked, size_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_size_checked, size_t, 100, ACTUAL_MAX - 99);
    CHECK_OVF(aws_add_size_checked, size_t, 100, ACTUAL_MAX - 1);
    return 0;
}

AWS_TEST_CASE(test_add_size_saturating, s_test_add_size_saturating_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_size_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

#if SIZE_MAX == UINT32_MAX
    const uint32_t HALF_MAX = UINT32_MAX / 2;
    const uint32_t ACTUAL_MAX = UINT32_MAX;
#elif SIZE_MAX == UINT64_MAX
    const uint64_t HALF_MAX = UINT64_MAX / 2;
    const uint64_t ACTUAL_MAX = UINT64_MAX;
#else
    FAIL("Unexpected size for size_t: %zu", sizeof(size_t));
#endif
    (void)HALF_MAX;
    (void)ACTUAL_MAX;
    /* No overflow expected */
    CHECK_SAT(aws_add_size_saturating, 0, 0, 0);
    CHECK_SAT(aws_add_size_saturating, 0, 1, 1);
    CHECK_SAT(aws_add_size_saturating, 4, 5, 9);
    CHECK_SAT(aws_add_size_saturating, 1234, 4321, 5555);
    CHECK_SAT(aws_add_size_saturating, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_SAT(aws_add_size_saturating, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    /* Overflow expected */
    CHECK_SAT(aws_add_size_saturating, 1, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, 100, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, ACTUAL_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX + 1, HALF_MAX + 1, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, 100, ACTUAL_MAX - 99, ACTUAL_MAX);
    CHECK_SAT(aws_add_size_saturating, 100, ACTUAL_MAX - 1, ACTUAL_MAX);
    return 0;
}

AWS_TEST_CASE(test_add_u32_checked, s_test_add_u32_checked_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_u32_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    const uint32_t HALF_MAX = UINT32_MAX / 2;
    const uint32_t ACTUAL_MAX = UINT32_MAX;
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 0, 0, 0);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 0, 1, 1);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 4, 5, 9);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 1234, 4321, 5555);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_NO_OVF(aws_add_u32_checked, uint32_t, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    CHECK_OVF(aws_add_u32_checked, uint32_t, 1, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, 100, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, HALF_MAX + 1, HALF_MAX + 1);
    CHECK_OVF(aws_add_u32_checked, uint32_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u32_checked, uint32_t, 100, ACTUAL_MAX - 99);
    CHECK_OVF(aws_add_u32_checked, uint32_t, 100, ACTUAL_MAX - 1);
    return 0;
}

AWS_TEST_CASE(test_add_u32_saturating, s_test_add_u32_saturating_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_u32_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    const uint32_t HALF_MAX = UINT32_MAX / 2;
    const uint32_t ACTUAL_MAX = UINT32_MAX;

    /* No overflow expected */
    CHECK_SAT(aws_add_u32_saturating, 0, 0, 0);
    CHECK_SAT(aws_add_u32_saturating, 0, 1, 1);
    CHECK_SAT(aws_add_u32_saturating, 4, 5, 9);
    CHECK_SAT(aws_add_u32_saturating, 1234, 4321, 5555);
    CHECK_SAT(aws_add_u32_saturating, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_SAT(aws_add_u32_saturating, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    /* Overflow expected */
    CHECK_SAT(aws_add_u32_saturating, 1, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, 100, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, ACTUAL_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX + 1, HALF_MAX + 1, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, 100, ACTUAL_MAX - 99, ACTUAL_MAX);
    CHECK_SAT(aws_add_u32_saturating, 100, ACTUAL_MAX - 1, ACTUAL_MAX);
    return 0;
}

AWS_TEST_CASE(test_add_u64_checked, s_test_add_u64_checked_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_u64_checked_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    const uint64_t HALF_MAX = UINT64_MAX / 2;
    const uint64_t ACTUAL_MAX = UINT64_MAX;
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 0, 0, 0);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 0, 1, 1);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 4, 5, 9);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 1234, 4321, 5555);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_NO_OVF(aws_add_u64_checked, uint64_t, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    CHECK_OVF(aws_add_u64_checked, uint64_t, 1, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, 100, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, HALF_MAX + 1, HALF_MAX + 1);
    CHECK_OVF(aws_add_u64_checked, uint64_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, HALF_MAX, ACTUAL_MAX);
    CHECK_OVF(aws_add_u64_checked, uint64_t, 100, ACTUAL_MAX - 99);
    CHECK_OVF(aws_add_u64_checked, uint64_t, 100, ACTUAL_MAX - 1);
    return 0;
}

AWS_TEST_CASE(test_add_u64_saturating, s_test_add_u64_saturating_fn)
/* NOLINTNEXTLINE(readability-function-size) */
static int s_test_add_u64_saturating_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    const uint64_t HALF_MAX = UINT64_MAX / 2;
    const uint64_t ACTUAL_MAX = UINT64_MAX;

    /* No overflow expected */
    CHECK_SAT(aws_add_u64_saturating, 0, 0, 0);
    CHECK_SAT(aws_add_u64_saturating, 0, 1, 1);
    CHECK_SAT(aws_add_u64_saturating, 4, 5, 9);
    CHECK_SAT(aws_add_u64_saturating, 1234, 4321, 5555);
    CHECK_SAT(aws_add_u64_saturating, 0, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX, HALF_MAX, ACTUAL_MAX - 1);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX + 1, HALF_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, 100, ACTUAL_MAX - 102, ACTUAL_MAX - 2);
    CHECK_SAT(aws_add_u64_saturating, 100, ACTUAL_MAX - 100, ACTUAL_MAX);

    /* Overflow expected */
    CHECK_SAT(aws_add_u64_saturating, 1, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, 100, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, ACTUAL_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX + 1, HALF_MAX + 1, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, HALF_MAX, ACTUAL_MAX, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, 100, ACTUAL_MAX - 99, ACTUAL_MAX);
    CHECK_SAT(aws_add_u64_saturating, 100, ACTUAL_MAX - 1, ACTUAL_MAX);
    return 0;
}
