/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/environment.h>

#include <aws/common/string.h>

#include <aws/testing/aws_test_harness.h>

AWS_STATIC_STRING_FROM_LITERAL(s_test_variable, "AWS_TEST_VAR");

AWS_STATIC_STRING_FROM_LITERAL(s_test_value, "SOME_VALUE");

static int s_test_environment_functions_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_string *value;

    int result = aws_get_environment_value(allocator, s_test_variable, &value);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);
    ASSERT_TRUE(value == NULL);

    result = aws_set_environment_value(s_test_variable, (struct aws_string *)s_test_value);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);

    result = aws_get_environment_value(allocator, s_test_variable, &value);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);
    ASSERT_TRUE(aws_string_compare(value, s_test_value) == 0);

    aws_string_destroy(value);

    result = aws_unset_environment_value(s_test_variable);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);

    result = aws_get_environment_value(allocator, s_test_variable, &value);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);
    ASSERT_TRUE(value == NULL);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_environment_functions, s_test_environment_functions_fn)
