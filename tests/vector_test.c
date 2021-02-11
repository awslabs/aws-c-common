/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/vector.h>

#include <aws/testing/aws_test_harness.h>

DECLARE_VECTOR(aws_float_vector, float)

static int s_typed_vector_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_float_vector v;
    aws_float_vector_init(&v, allocator);
    ASSERT_UINT_EQUALS(0, aws_float_vector_length(&v));
    ASSERT_TRUE(aws_float_vector_empty(&v));

    /* push in some items */
    aws_float_vector_push_back(&v, 0.0f);
    aws_float_vector_push_back(&v, 1.1f);
    ASSERT_UINT_EQUALS(2, aws_float_vector_length(&v));
    ASSERT_FALSE(aws_float_vector_empty(&v));

    float *data = aws_float_vector_data(&v);
    ASSERT_TRUE(data[0] == 0.0f);
    ASSERT_TRUE(data[1] == 1.1f);

    ASSERT_TRUE(0.0f == aws_float_vector_get(&v, 0));
    ASSERT_TRUE(1.1f == aws_float_vector_get(&v, 1));

    float *idx0_ptr = aws_float_vector_get_ptr(&v, 0);
    float *idx1_ptr = aws_float_vector_get_ptr(&v, 1);
    ASSERT_PTR_EQUALS(data, idx0_ptr);
    ASSERT_TRUE(0.0f == *idx0_ptr);
    ASSERT_TRUE(1.1f == *idx1_ptr);

    /* change an item */
    aws_float_vector_set(&v, 1, 111.1f);
    ASSERT_TRUE(111.1f == aws_float_vector_get(&v, 1));

    aws_float_vector_clean_up(&v);
    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(typed_vector, s_typed_vector_test_fn)
