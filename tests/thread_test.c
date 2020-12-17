/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

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
