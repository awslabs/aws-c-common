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

int do_log_test(
    struct aws_allocator *allocator,
    enum aws_log_level level,
    const char *expected_result,
    void (*callback)(enum aws_log_level)) {

    /* Create and attach a logger for testing*/
    struct aws_logger test_logger;
    test_logger_init(&test_logger, allocator, level);
    aws_logger_set(&test_logger);

    /* Perform logging operations */
    (*callback)(level);

    /* Pull out what was logged before clean up */
    char buffer[TEST_LOGGER_MAX_BUFFER_SIZE];
    test_logger_get_contents(&test_logger, buffer, TEST_LOGGER_MAX_BUFFER_SIZE);

    /* clean up */
    aws_logger_set(NULL);
    aws_logger_clean_up(&test_logger);

    /* Check the test results last */
    ASSERT_SUCCESS(strcmp(buffer, expected_result), "Expected \"%s\" but received \"%s\"", expected_result, buffer);

    return AWS_OP_SUCCESS;
}
