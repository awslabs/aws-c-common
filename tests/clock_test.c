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

#include <aws/common/clock.h>

#include <aws/common/thread.h>
#include <aws/testing/aws_test_harness.h>

static int test_high_res_clock_increments(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ticks = 0, prev = 0;

    for (unsigned i = 0; i < 100; ++i) {
        ASSERT_SUCCESS(
            aws_high_res_clock_get_ticks(&ticks), "High res get ticks failed with error %d", aws_last_error());
        ASSERT_TRUE(
            ticks >= prev,
            "Next get ticks should have been greater than or equal to "
            "previous. previous %llu current %llu",
            (long long unsigned int)prev,
            (long long unsigned int)ticks);
        aws_thread_current_sleep(1000000);
        prev = ticks;
    }

    return 0;
}

static int test_sys_clock_increments(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ticks = 0, prev = 0;

    for (unsigned i = 0; i < 100; ++i) {
        ASSERT_SUCCESS(
            aws_sys_clock_get_ticks(&ticks), "Sys clock res get ticks failed with error %d", aws_last_error());
        ASSERT_TRUE(
            ticks >= prev,
            "Next get ticks should have been greater than or equal to "
            "previous. previous %llu current %llu",
            (long long unsigned int)prev,
            (long long unsigned int)ticks);
        aws_thread_current_sleep(1000000);
        prev = ticks;
    }

    return 0;
}

AWS_TEST_CASE(high_res_clock_increments_test, test_high_res_clock_increments)
AWS_TEST_CASE(sys_clock_increments_test, test_sys_clock_increments)
