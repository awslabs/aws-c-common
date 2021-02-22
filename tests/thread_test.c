/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
#include <aws/common/private/thread_shared.h>
#include <aws/common/thread.h>

#include <aws/testing/aws_test_harness.h>

struct thread_test_data {
    aws_thread_id_t thread_id;
};

static void s_thread_fn(void *arg) {
    struct thread_test_data *test_data = (struct thread_test_data *)arg;
    test_data->thread_id = aws_thread_current_thread_id();
}

static int s_test_thread_creation_join_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);
    struct thread_test_data test_data;

    struct aws_thread thread;
    aws_thread_init(&thread, allocator);

    struct aws_thread_options thread_options = *aws_default_thread_options();
    /* there should be at least 1 cpu on any machine running this test. Just bind that to make sure that code
     * path is exercised. */
    thread_options.cpu_id = 0;

    ASSERT_SUCCESS(
        aws_thread_launch(&thread, s_thread_fn, (void *)&test_data, &thread_options), "thread creation failed");
    ASSERT_INT_EQUALS(
        AWS_THREAD_JOINABLE, aws_thread_get_detach_state(&thread), "thread state should have returned JOINABLE");
    ASSERT_SUCCESS(aws_thread_join(&thread), "thread join failed");
    ASSERT_TRUE(
        aws_thread_thread_id_equal(test_data.thread_id, aws_thread_get_id(&thread)),
        "get_thread_id should have returned the same id as the thread calling current_thread_id");
    ASSERT_INT_EQUALS(
        AWS_THREAD_JOIN_COMPLETED,
        aws_thread_get_detach_state(&thread),
        "thread state should have returned JOIN_COMPLETED");

    aws_thread_clean_up(&thread);
    aws_common_library_clean_up();

    return 0;
}

AWS_TEST_CASE(thread_creation_join_test, s_test_thread_creation_join_fn)

static uint32_t s_atexit_call_count = 0;
static void s_thread_atexit_fn(void *user_data) {
    (void)user_data;
    AWS_FATAL_ASSERT(s_atexit_call_count == 0);
    s_atexit_call_count = 1;
}

static void s_thread_atexit_fn2(void *user_data) {
    (void)user_data;
    AWS_FATAL_ASSERT(s_atexit_call_count == 1);
    s_atexit_call_count = 2;
}

static void s_thread_worker_with_atexit(void *arg) {
    (void)arg;
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_thread_current_at_exit(s_thread_atexit_fn2, NULL));
    AWS_FATAL_ASSERT(AWS_OP_SUCCESS == aws_thread_current_at_exit(s_thread_atexit_fn, NULL));
}

static int s_test_thread_atexit(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_thread thread;
    ASSERT_SUCCESS(aws_thread_init(&thread, allocator));

    ASSERT_SUCCESS(aws_thread_launch(&thread, s_thread_worker_with_atexit, NULL, 0), "thread creation failed");
    ASSERT_SUCCESS(aws_thread_join(&thread), "thread join failed");

    ASSERT_INT_EQUALS(2, s_atexit_call_count);

    aws_thread_clean_up(&thread);

    return 0;
}

AWS_TEST_CASE(thread_atexit_test, s_test_thread_atexit)

struct managed_thread_test_data {
    uint64_t sleep_time_in_ns;
};

static void s_managed_thread_fn(void *arg) {
    struct managed_thread_test_data *test_data = (struct managed_thread_test_data *)arg;

    aws_thread_current_sleep(test_data->sleep_time_in_ns);
}

#define MAX_MANAGED_THREAD_TEST_QUANTITY 16

static int s_do_managed_thread_join_test(struct aws_allocator *allocator, size_t thread_count) {

    struct aws_thread threads[MAX_MANAGED_THREAD_TEST_QUANTITY];
    struct managed_thread_test_data thread_data[MAX_MANAGED_THREAD_TEST_QUANTITY];

    AWS_FATAL_ASSERT(thread_count <= MAX_MANAGED_THREAD_TEST_QUANTITY);

    for (size_t i = 0; i < thread_count; ++i) {
        thread_data[i].sleep_time_in_ns =
            aws_timestamp_convert(100 * (i / 2), AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_NANOS, NULL);
        aws_thread_init(&threads[i], allocator);
    }

    struct aws_thread_options thread_options = *aws_default_thread_options();
    thread_options.join_strategy = AWS_TJS_MANAGED;

    for (size_t i = 0; i < thread_count; ++i) {
        ASSERT_SUCCESS(
            aws_thread_launch(&threads[i], s_managed_thread_fn, (void *)&thread_data[i], &thread_options),
            "thread creation failed");

        aws_thread_clean_up(&threads[i]);

        ASSERT_INT_EQUALS(
            AWS_THREAD_MANAGED, aws_thread_get_detach_state(&threads[i]), "thread state should have returned JOINABLE");
    }

    aws_thread_join_all_managed();

    return AWS_OP_SUCCESS;
}

static int s_test_managed_thread_join(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);

    for (size_t i = 1; i <= MAX_MANAGED_THREAD_TEST_QUANTITY; ++i) {
        ASSERT_SUCCESS(s_do_managed_thread_join_test(allocator, i));
    }

    aws_common_library_clean_up();

    return 0;
}

AWS_TEST_CASE(test_managed_thread_join, s_test_managed_thread_join)

/*
 * Because this is unmocked time, this is technically not a purely deterministic test, but we set the time values
 * to extreme enough values that it should absurdly unlikely that an internal OS/CPU hiccup causes this test to fail.
 */
static int s_test_managed_thread_join_timeout(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);

    /*
     * Add a short timeout to managed thread join
     */
    aws_thread_set_managed_join_timeout_ns(aws_timestamp_convert(1, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_NANOS, NULL));

    /*
     * Spawn a managed thread that sleeps for significantly longer.
     */
    struct managed_thread_test_data thread_data;
    AWS_ZERO_STRUCT(thread_data);
    thread_data.sleep_time_in_ns = aws_timestamp_convert(3, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_NANOS, NULL);

    struct aws_thread thread;
    AWS_ZERO_STRUCT(thread);
    aws_thread_init(&thread, allocator);

    struct aws_thread_options thread_options = *aws_default_thread_options();
    thread_options.join_strategy = AWS_TJS_MANAGED;

    ASSERT_SUCCESS(
        aws_thread_launch(&thread, s_managed_thread_fn, (void *)&thread_data, &thread_options),
        "thread creation failed");

    aws_thread_clean_up(&thread);

    ASSERT_TRUE(aws_thread_get_managed_thread_count() == 1);

    /*
     * Do a managed thread join, it should timeout
     */
    aws_thread_join_all_managed();

    /*
     * Check that the managed thread is still running
     */
    ASSERT_TRUE(aws_thread_get_managed_thread_count() == 1);

    /*
     * Increase the timeout and shut down
     */
    aws_thread_set_managed_join_timeout_ns(aws_timestamp_convert(5, AWS_TIMESTAMP_SECS, AWS_TIMESTAMP_NANOS, NULL));

    aws_common_library_clean_up();

    ASSERT_TRUE(aws_thread_get_managed_thread_count() == 0);

    return 0;
}

AWS_TEST_CASE(test_managed_thread_join_timeout, s_test_managed_thread_join_timeout)
