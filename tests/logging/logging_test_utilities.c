/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "logging_test_utilities.h"

#include "test_logger.h"

int do_log_test(enum aws_log_level level, const char *expected_result, void (*callback)(enum aws_log_level)) {
    struct aws_logger test_logger;
    test_logger_init(&test_logger, aws_default_allocator(), level);
    aws_logging_set(&test_logger);

    (*callback)(level);

    char buffer[TEST_LOGGER_MAX_BUFFER_SIZE];
    test_logger_get_contents(&test_logger, buffer, TEST_LOGGER_MAX_BUFFER_SIZE);

    aws_logging_set(NULL);
    test_logger_cleanup(&test_logger);

    ASSERT_SUCCESS(strcmp(buffer, expected_result), "Expected \"%s\" but received \"%s\"", expected_result, buffer);

    return AWS_OP_SUCCESS;
}

void log_all_levels_v1(enum aws_log_level level) {
    for (int i = 0; i < AWS_LL_COUNT; ++i) {
        LOGF(i, "%d", i)
    }
}

void log_all_levels_v2(enum aws_log_level level) {
    LOGF_FATAL("%d", (int)AWS_LL_FATAL)
    LOGF_ERROR("%d", (int)AWS_LL_ERROR)
    LOGF_WARN("%d", (int)AWS_LL_WARN)
    LOGF_INFO("%d", (int)AWS_LL_INFO)
    LOGF_DEBUG("%d", (int)AWS_LL_DEBUG)
    LOGF_TRACE("%d", (int)AWS_LL_TRACE)
}
