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

#if defined(__MACH__)
#    include <AvailabilityMacros.h>
#endif

#if defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200
#    include <sys/time.h>
#endif /*defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200*/

static const uint64_t NS_PER_SEC = 1000000000;

#if defined(CLOCK_MONOTONIC_RAW)
#    define HIGH_RES_CLOCK CLOCK_MONOTONIC_RAW
#else
#    define HIGH_RES_CLOCK CLOCK_MONOTONIC
#endif

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    int ret_val = 0;

#if defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200
    struct timeval tv;
    ret_val = gettimeofday(&tv, NULL);

    if (ret_val) {
        return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
    }

    *timestamp = tv.tv_sec * NS_PER_SEC + tv.tv_usec * 1000;
#else
    struct timespec ts;

    ret_val = clock_gettime(HIGH_RES_CLOCK, &ts);

    if (ret_val) {
        return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
    }

    *timestamp = (uint64_t)((ts.tv_sec * NS_PER_SEC) + ts.tv_nsec);
#endif /*defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200*/

    return AWS_OP_SUCCESS;
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
#if defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200
    return aws_high_res_clock_get_ticks(timestamp);
#else
    int ret_val = 0;

    struct timespec ts;
    ret_val = clock_gettime(CLOCK_REALTIME, &ts);
    if (ret_val) {
        return aws_raise_error(AWS_ERROR_CLOCK_FAILURE);
    }

    *timestamp = (uint64_t)((ts.tv_sec * NS_PER_SEC) + ts.tv_nsec);
#endif /*defined(__MACH__) && MAC_OS_X_VERSION_MAX_ALLOWED < 101200*/

    return AWS_OP_SUCCESS;
}
