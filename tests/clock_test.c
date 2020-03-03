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

static int s_test_high_res_clock_increments(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ticks = 0, prev = 0;

    for (unsigned i = 0; i < 100; ++i) {
        ASSERT_SUCCESS(
            aws_high_res_clock_get_ticks(&ticks), "High res get ticks failed with error %d", aws_last_error());
        ASSERT_TRUE(
            ticks >= prev,
            "Next get ticks should have been greater than or equal to previous. previous %llu current %llu",
            (long long unsigned int)prev,
            (long long unsigned int)ticks);
        aws_thread_current_sleep(1000000);
        prev = ticks;
    }

    return 0;
}

static int s_test_sys_clock_increments(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ticks = 0, prev = 0;

    for (unsigned i = 0; i < 100; ++i) {
        ASSERT_SUCCESS(
            aws_sys_clock_get_ticks(&ticks), "Sys clock res get ticks failed with error %d", aws_last_error());
        ASSERT_TRUE(
            ticks >= prev,
            "Next get ticks should have been greater than or equal to previous. previous %llu current %llu",
            (long long unsigned int)prev,
            (long long unsigned int)ticks);
        aws_thread_current_sleep(1000000);
        prev = ticks;
    }

    return 0;
}

static int s_test_sec_and_millis_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t secs = 10;
    ASSERT_UINT_EQUALS(10000, aws_timestamp_convert(secs, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_MILLIS, NULL));
    ASSERT_UINT_EQUALS(secs, aws_timestamp_convert(10000, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_SECS, NULL));

    return 0;
}

static int s_test_sec_and_micros_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t secs = 10;
    ASSERT_UINT_EQUALS(10000000, aws_timestamp_convert(secs, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_MICROS, NULL));
    ASSERT_UINT_EQUALS(secs, aws_timestamp_convert(10000000, AWS_TIMESTAMP_MICROS, AWS_TIMESTAMP_SECS, NULL));

    return 0;
}

static int s_test_sec_and_nanos_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t secs = 10;
    ASSERT_UINT_EQUALS(10000000000, aws_timestamp_convert(secs, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_NANOS, NULL));
    ASSERT_UINT_EQUALS(secs, aws_timestamp_convert(10000000000, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_SECS, NULL));

    return 0;
}

static int s_test_milli_and_micros_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ms = 10;
    ASSERT_UINT_EQUALS(10000, aws_timestamp_convert(ms, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_MICROS, NULL));
    ASSERT_UINT_EQUALS(ms, aws_timestamp_convert(10000, AWS_TIMESTAMP_MICROS, AWS_TIMESTAMP_MILLIS, NULL));

    return 0;
}

static int s_test_milli_and_nanos_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t ms = 10;
    ASSERT_UINT_EQUALS(10000000, aws_timestamp_convert(ms, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_NANOS, NULL));
    ASSERT_UINT_EQUALS(ms, aws_timestamp_convert(10000000, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MILLIS, NULL));

    return 0;
}

static int s_test_micro_and_nanos_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t micros = 10;
    ASSERT_UINT_EQUALS(10000, aws_timestamp_convert(micros, AWS_TIMESTAMP_MICROS, AWS_TIMESTAMP_NANOS, NULL));
    ASSERT_UINT_EQUALS(micros, aws_timestamp_convert(10000, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MICROS, NULL));

    return 0;
}

static int s_test_precision_loss_remainders_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t nanos = 10123456789;
    uint64_t remainder = 0;
    ASSERT_UINT_EQUALS(10, aws_timestamp_convert(nanos, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_SECS, &remainder));
    ASSERT_UINT_EQUALS(123456789, remainder);

    return 0;
}

static int s_test_overflow_conversion(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000ULL, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_NANOS, NULL));

    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000000ULL, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_MICROS, NULL));
    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000000ULL, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_NANOS, NULL));

    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000000000ULL, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_MILLIS, NULL));
    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000000000ULL, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_MICROS, NULL));
    ASSERT_UINT_EQUALS(
        UINT64_MAX, aws_timestamp_convert(100000000000000000ULL, AWS_TIMESTAMP_MICROS, AWS_TIMESTAMP_NANOS, NULL));
    return 0;
}

AWS_TEST_CASE(high_res_clock_increments_test, s_test_high_res_clock_increments)
AWS_TEST_CASE(sys_clock_increments_test, s_test_sys_clock_increments)
AWS_TEST_CASE(test_sec_and_millis_conversions, s_test_sec_and_millis_conversion)
AWS_TEST_CASE(test_sec_and_micros_conversions, s_test_sec_and_micros_conversion)
AWS_TEST_CASE(test_sec_and_nanos_conversions, s_test_sec_and_nanos_conversion)
AWS_TEST_CASE(test_milli_and_micros_conversion, s_test_milli_and_micros_conversion)
AWS_TEST_CASE(test_milli_and_nanos_conversion, s_test_milli_and_nanos_conversion)
AWS_TEST_CASE(test_micro_and_nanos_conversion, s_test_micro_and_nanos_conversion)
AWS_TEST_CASE(test_precision_loss_remainders_conversion, s_test_precision_loss_remainders_conversion)
AWS_TEST_CASE(test_overflow_conversion, s_test_overflow_conversion)

static uint64_t s_high_res_time = 0;
int s_mock_high_res_clock_fn(uint64_t *time) {
    *time = s_high_res_time;

    return AWS_OP_SUCCESS;
}

static uint64_t s_system_time = 0;
int s_mock_system_clock_fn(uint64_t *time) {
    *time = s_system_time;

    return AWS_OP_SUCCESS;
}

static int s_test_override_system_vtable(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    s_high_res_time = 1;
    s_system_time = 2;

    struct aws_clock_system_vtable good_table = {
        .high_res_clock = s_mock_high_res_clock_fn,
        .system_clock = s_mock_system_clock_fn,
    };
    aws_clock_set_system_vtable(&good_table);

    uint64_t time = 0;
    ASSERT_SUCCESS(aws_sys_clock_get_ticks(&time));
    ASSERT_TRUE(time == 2);
    ASSERT_SUCCESS(aws_high_res_clock_get_ticks(&time));
    ASSERT_TRUE(time == 1);

    struct aws_clock_system_vtable bad_high_res_table = {
        .high_res_clock = NULL,
        .system_clock = s_mock_system_clock_fn,
    };
    aws_clock_set_system_vtable(&bad_high_res_table);
    ASSERT_FAILS(aws_high_res_clock_get_ticks(&time));

    struct aws_clock_system_vtable bad_sys_table = {
        .high_res_clock = s_mock_high_res_clock_fn,
        .system_clock = NULL,
    };
    aws_clock_set_system_vtable(&bad_sys_table);
    ASSERT_FAILS(aws_sys_clock_get_ticks(&time));

    return 0;
}

AWS_TEST_CASE(test_override_system_vtable, s_test_override_system_vtable)
