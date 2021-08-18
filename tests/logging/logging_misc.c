/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/logging.h>

#include <aws/testing/aws_test_harness.h>

static int s_string_to_log_level_success_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;

    enum aws_log_level level = AWS_LL_NONE;

    ASSERT_SUCCESS(aws_string_to_log_level("DeBug", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_DEBUG);

    ASSERT_SUCCESS(aws_string_to_log_level("TRACE", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_TRACE);

    ASSERT_SUCCESS(aws_string_to_log_level("warn", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_WARN);

    ASSERT_SUCCESS(aws_string_to_log_level("InFo", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_INFO);

    ASSERT_SUCCESS(aws_string_to_log_level("errOr", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_ERROR);

    ASSERT_SUCCESS(aws_string_to_log_level("FATAL", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_FATAL);

    ASSERT_SUCCESS(aws_string_to_log_level("none", &level));
    ASSERT_INT_EQUALS(level, AWS_LL_NONE);

    return 0;
}
AWS_TEST_CASE(string_to_log_level_success_test, s_string_to_log_level_success_test)

static int s_string_to_log_level_failure_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;

    enum aws_log_level level = AWS_LL_NONE;

    ASSERT_FAILS(aws_string_to_log_level("", &level));
    ASSERT_FAILS(aws_string_to_log_level("Tracee", &level));
    ASSERT_FAILS(aws_string_to_log_level("war", &level));
    ASSERT_FAILS(aws_string_to_log_level("Not a log level", &level));
    ASSERT_FAILS(aws_string_to_log_level(NULL, &level));
    ASSERT_FAILS(aws_string_to_log_level(NULL, NULL));
    ASSERT_FAILS(aws_string_to_log_level("FATAL", NULL));

    return 0;
}
AWS_TEST_CASE(string_to_log_level_failure_test, s_string_to_log_level_failure_test)
