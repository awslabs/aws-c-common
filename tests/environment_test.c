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

static int s_test_env_functions_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *env_name = aws_string_c_str(s_test_variable);
    struct aws_string *value = aws_get_env(allocator, env_name);
    ASSERT_TRUE(value == NULL);

    value = aws_get_env_nonempty(allocator, env_name);
    ASSERT_TRUE(value == NULL);

    int result = aws_set_environment_value(s_test_variable, (struct aws_string *)s_test_value);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);

    value = aws_get_env(allocator, env_name);
    ASSERT_TRUE(aws_string_compare(value, s_test_value) == 0);
    aws_string_destroy(value);

    value = aws_get_env_nonempty(allocator, env_name);
    ASSERT_TRUE(aws_string_compare(value, s_test_value) == 0);
    aws_string_destroy(value);

    struct aws_string *empty_str = aws_string_new_from_c_str(allocator, "");
    result = aws_set_environment_value(s_test_variable, empty_str);
    ASSERT_TRUE(result == AWS_OP_SUCCESS);

    value = aws_get_env(allocator, env_name);
#ifndef AWS_OS_WINDOWS
    ASSERT_TRUE(aws_string_compare(value, empty_str) == 0);
#endif
    aws_string_destroy(value);

    value = aws_get_env_nonempty(allocator, env_name);
    ASSERT_TRUE(value == NULL);

    aws_string_destroy(empty_str);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_env_functions, s_test_env_functions_fn)
