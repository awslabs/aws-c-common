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

#include <aws/common/process.h>
#include <aws/common/string.h>
#include <aws/testing/aws_test_harness.h>

static int s_get_pid_sanity_check_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    int pid = aws_get_pid();
    ASSERT_TRUE(pid > 0);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(get_pid_sanity_check_test, s_get_pid_sanity_check_test_fn)

#ifdef _WIN32
AWS_STATIC_STRING_FROM_LITERAL(s_test_command, "echo {\"Version\": 1, \"AccessKeyId\": \"AccessKey123\"}");
#else
AWS_STATIC_STRING_FROM_LITERAL(s_test_command, "echo '{\"Version\": 1, \"AccessKeyId\": \"AccessKey123\"}'");
#endif
AWS_STATIC_STRING_FROM_LITERAL(s_expected_output, "{\"Version\": 1, \"AccessKeyId\": \"AccessKey123\"}");

static int s_run_command_test_success_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_run_command_options options = {.command = aws_string_c_str(s_test_command)};

    struct aws_run_command_result result;
    ASSERT_SUCCESS(aws_run_command_result_init(allocator, &result));
    ASSERT_SUCCESS(aws_run_command(allocator, &options, &result));
    ASSERT_TRUE(result.ret_code == 0);
    ASSERT_NOT_NULL(result.std_out);

    ASSERT_BIN_ARRAYS_EQUALS(
        result.std_out->bytes, result.std_out->len, s_expected_output->bytes, s_expected_output->len);

    aws_run_command_result_cleanup(&result);
    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(run_command_test_success, s_run_command_test_success_fn)

AWS_STATIC_STRING_FROM_LITERAL(s_bad_command, "/i/dont/know/what/is/this/command");
static int s_run_command_test_bad_command_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_run_command_options options = {.command = aws_string_c_str(s_bad_command)};

    struct aws_run_command_result result;
    ASSERT_SUCCESS(aws_run_command_result_init(allocator, &result));
    ASSERT_SUCCESS(aws_run_command(allocator, &options, &result));
    ASSERT_TRUE(result.ret_code != 0);
    ASSERT_NULL(result.std_out);

    aws_run_command_result_cleanup(&result);
    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(run_command_test_bad_command, s_run_command_test_bad_command_fn)