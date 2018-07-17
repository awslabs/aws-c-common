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

#include <aws/common/log.h>
#include <aws/testing/aws_test_harness.h>

static void log_report_fn(const char* log_message) {
    fprintf(AWS_TESTING_REPORT_FD, log_message);
}

AWS_TEST_CASE(test_log_init_clean_up, test_log_init_clean_up_fn)
static int test_log_init_clean_up_fn(struct aws_allocator *allocator, void *ctx) {
    const int message_len = 1024;
    const int max_messages = 256;

    uint64_t id = aws_thread_current_thread_id();
    id = 0;

    ASSERT_SUCCESS(aws_log_init(allocator, message_len, max_messages));
    aws_log_set_reporting_callback(log_report_fn);

    ASSERT_SUCCESS(aws_log(AWS_LOG_LEVEL_TRACE, "Oh, hello there #1.\n"));
    ASSERT_SUCCESS(aws_log_process());
    ASSERT_SUCCESS(aws_log(AWS_LOG_LEVEL_TRACE, "Oh, hello there #2.\n"));
    ASSERT_SUCCESS(aws_log_process());
    ASSERT_SUCCESS(aws_log(AWS_LOG_LEVEL_TRACE, "Oh, hello there #3.\n"));
    ASSERT_SUCCESS(aws_log(AWS_LOG_LEVEL_TRACE, "Oh, hello there #4.\n"));
    ASSERT_SUCCESS(aws_log(AWS_LOG_LEVEL_TRACE, "Oh, hello there #5.\n"));
    ASSERT_SUCCESS(aws_log_process());

    ASSERT_SUCCESS(aws_log_clean_up());

    return 0;
}
