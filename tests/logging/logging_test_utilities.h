
#ifndef AWS_COMMON_LOGGING_TEST_UTILITIES_H
#define AWS_COMMON_LOGGING_TEST_UTILITIES_H

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

#include <aws/common/logging.h>

#include <aws/testing/aws_test_harness.h>

int do_log_test(enum aws_log_level level, const char *expected_result, void (*callback)(enum aws_log_level));

void log_all_levels_v1(enum aws_log_level level);
void log_all_levels_v2(enum aws_log_level level);

#define TEST_LEVEL_FILTER(log_level, expected, token) \
static int s_logging_filter_v1_at_##log_level##_##token##_fn(struct aws_allocator *allocator, void *ctx) { \
    (void) ctx; \
    return do_log_test(log_level, expected, log_all_levels_v1); \
} \
AWS_TEST_CASE(test_logging_filter_v1_at_##log_level##_##token, s_logging_filter_v1_at_##log_level##_##token##_fn); \
static int s_logging_filter_v2_at_##log_level##_##token##_fn(struct aws_allocator *allocator, void *ctx) { \
    (void) ctx; \
    return do_log_test(log_level, expected, log_all_levels_v2); \
} \
AWS_TEST_CASE(test_logging_filter_v2_at_##log_level##_##token, s_logging_filter_v2_at_##log_level##_##token##_fn);

#endif //AWS_COMMON_LOGGING_TEST_UTILITIES_H
