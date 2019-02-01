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

static void s_log_all_levels_v1(enum aws_log_level level) {
    for (int i = 0; i < AWS_LL_COUNT; ++i) {
        LOGF(i, "%d", i)
    }
}

static void s_log_all_levels_v2(enum aws_log_level level) {
    LOGF_FATAL("%d", (int)AWS_LL_FATAL)
    LOGF_ERROR("%d", (int)AWS_LL_ERROR)
    LOGF_WARN("%d", (int)AWS_LL_WARN)
    LOGF_INFO("%d", (int)AWS_LL_INFO)
    LOGF_DEBUG("%d", (int)AWS_LL_DEBUG)
    LOGF_TRACE("%d", (int)AWS_LL_TRACE)
}

TEST_LEVEL_FILTER(AWS_LL_TRACE, "123456", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_TRACE, "123456", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_DEBUG, "12345", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_DEBUG, "12345", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_INFO, "1234", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_INFO, "1234", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_WARN, "123", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_WARN, "123", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_ERROR, "12", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_ERROR, "12", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_FATAL, "1", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_FATAL, "1", s_log_all_levels_v2)
TEST_LEVEL_FILTER(AWS_LL_NONE, "", s_log_all_levels_v1)
TEST_LEVEL_FILTER(AWS_LL_NONE, "", s_log_all_levels_v2)

