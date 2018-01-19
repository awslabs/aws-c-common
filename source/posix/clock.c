/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/clock.h>
#include <time.h>

static const long NS_PER_SEC = 1000000000;

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    struct timespec ts;
    int ret_val = clock_gettime(CLOCK_MONOTONIC, &ts);
    if(ret_val) {
        return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
    }

    *timestamp = (uint64_t)((ts.tv_sec * NS_PER_SEC) + ts.tv_nsec);
    return AWS_OP_SUCCESS;
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
    struct timespec ts;
    int ret_val = clock_gettime(CLOCK_REALTIME, &ts);
    if(ret_val) {
        return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
    }

    *timestamp = (uint64_t)((ts.tv_sec * NS_PER_SEC) + ts.tv_nsec);
    return AWS_OP_SUCCESS;
}

