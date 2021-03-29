/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include "logging_test_utilities.h"
#include "test_logger.h"

DECLARE_LOGF_ALL_LEVELS_FUNCTION(s_logf_all_levels)

/**
 * These tests check the dynamic (run-time) filtering capabilities of the logging
 * system.
 *
 * In each case, we use the test logger and invoke a log operation at each supported level.
 * Using the level (integer value) itself as the log text, we can easily check to see
 * what got filtered and what got through.
 *
 * For example, when the log level is AWS_LL_INFO, we expect
 *   {AWS_LL_FATAL, AWS_LL_ERROR, AWS_LL_WARN, AWS_LL_INFO} calls to all go through ("1234")
 * but
 *   {AWS_LL_DEBUG, AWS_LL_TRACE} to be filtered out ("56")
 */
TEST_LEVEL_FILTER(AWS_LL_TRACE, "123456", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_DEBUG, "12345", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_INFO, "1234", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_WARN, "123", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_ERROR, "12", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_FATAL, "1", s_logf_all_levels)
TEST_LEVEL_FILTER(AWS_LL_NONE, "", s_logf_all_levels)

/*
 * Dynamic level change testing
 */

#define TEST_LOGGER_MAX_BUFFER_SIZE 4096

static int s_dynamic_log_level_change_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;

    /* Create and attach a logger for testing*/
    struct aws_logger test_logger;
    test_logger_init(&test_logger, allocator, AWS_LOG_LEVEL_ERROR, TEST_LOGGER_MAX_BUFFER_SIZE);
    aws_logger_set(&test_logger);

    /* Perform logging operations */
    s_logf_all_levels(AWS_LOG_LEVEL_DEBUG);

    aws_logger_set_log_level(&test_logger, AWS_LOG_LEVEL_DEBUG);

    s_logf_all_levels(AWS_LOG_LEVEL_DEBUG);

    aws_logger_set_log_level(&test_logger, AWS_LOG_LEVEL_WARN);

    s_logf_all_levels(AWS_LOG_LEVEL_DEBUG);

    /* Pull out what was logged before clean up */
    char buffer[TEST_LOGGER_MAX_BUFFER_SIZE];
    test_logger_get_contents(&test_logger, buffer, TEST_LOGGER_MAX_BUFFER_SIZE);

    /* clean up */
    aws_logger_set(NULL);
    aws_logger_clean_up(&test_logger);

    /* Check the test results last */
    static const char *expected_result = "1212345123";
    ASSERT_SUCCESS(strcmp(buffer, expected_result), "Expected \"%s\" but received \"%s\"", expected_result, buffer);

    return 0;
}
AWS_TEST_CASE(dynamic_log_level_change_test, s_dynamic_log_level_change_test)
