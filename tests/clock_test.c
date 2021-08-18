/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
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

#define ONE_MHZ 1000000ULL
#define THREE_MHZ 3000000ULL
#define TEN_MHZ 10000000ULL
#define SIXTEEN_MHZ 16000000ULL
#define ONE_GHZ 1000000000ULL
#define TWO_GHZ 2000000000ULL
#define THIRTY_DAYS_IN_SECONDS (30ULL * 24 * 3600)
#define SIXTY_DAYS_IN_SECONDS (60ULL * 24 * 3600)
#define FIVE_YEARS_IN_SECONDS (5ULL * 365 * 24 * 3600)

/*
 * A test for a variety of edge cases that would unnecessarily overflow the old conversion logic.
 */
static int s_test_old_overflow_cases(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t timestamp = 0;

    /*
     * https://github.com/awslabs/aws-c-common/issues/790
     */
    timestamp = aws_timestamp_convert_u64(18446744073710ULL, ONE_MHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 18446744073710000ULL);

    /*
     * 30 days of ticks at 3Mhz to nanos: https://github.com/awslabs/aws-c-common/pull/791#issuecomment-821784745
     */
    timestamp = aws_timestamp_convert_u64(THIRTY_DAYS_IN_SECONDS * THREE_MHZ, THREE_MHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 2592000000000000ULL);

    /*
     * Same duration, but at 16Mhz
     */
    timestamp = aws_timestamp_convert_u64(THIRTY_DAYS_IN_SECONDS * SIXTEEN_MHZ, SIXTEEN_MHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 2592000000000000ULL);

    /*
     * 60 days at 1ghz (could be shortcutted internally since frequencies are equal)
     */
    timestamp = aws_timestamp_convert_u64(SIXTY_DAYS_IN_SECONDS * ONE_GHZ, ONE_GHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 5184000000000000ULL);

    /*
     * 60 days at 2ghz
     */
    timestamp = aws_timestamp_convert_u64(SIXTY_DAYS_IN_SECONDS * TWO_GHZ, TWO_GHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 5184000000000000ULL);

    /*
     * 60 days at 2ghz with a little bit more for some remainder
     */
    timestamp = aws_timestamp_convert_u64(SIXTY_DAYS_IN_SECONDS * TWO_GHZ + 123, TWO_GHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 5184000000000061ULL);

    /*
     * Five years at 10mhz + remainder
     */
    timestamp = aws_timestamp_convert_u64(FIVE_YEARS_IN_SECONDS * TEN_MHZ + 5, TEN_MHZ, AWS_TIMESTAMP_NANOS, NULL);
    ASSERT_UINT_EQUALS(timestamp, 157680000000000500ULL);

    /*
     * large ns -> 1mhz
     */
    timestamp = aws_timestamp_convert_u64(THIRTY_DAYS_IN_SECONDS * ONE_GHZ + 123456789, ONE_GHZ, ONE_MHZ, NULL);
    ASSERT_UINT_EQUALS(timestamp, 2592000000000ULL + 123456);

    /*
     * large ns -> 3mhz
     */
    timestamp = aws_timestamp_convert_u64(FIVE_YEARS_IN_SECONDS * ONE_GHZ + 1001, ONE_GHZ, THREE_MHZ, NULL);
    ASSERT_UINT_EQUALS(timestamp, 473040000000000ULL + 3);

    return 0;
}

AWS_TEST_CASE(test_old_overflow_cases, s_test_old_overflow_cases)
