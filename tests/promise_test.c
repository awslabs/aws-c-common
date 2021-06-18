/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
#include <aws/common/promise.h>
#include <aws/common/thread.h>

#include <aws/testing/aws_test_harness.h>

struct promise_test_work {
    struct aws_allocator *allocator;
    struct aws_promise *promise;
    uint64_t work_time;
    int error_code;
    void *value;
    void (*dtor)(void *);
};

static void s_promise_test_worker(void *data) {
    struct promise_test_work *work = data;
    aws_promise_acquire(work->promise);
    aws_thread_current_sleep(work->work_time);
    if (work->error_code) {
        aws_promise_fail(work->promise, work->error_code);
    } else {
        aws_promise_complete(work->promise, work->value, work->dtor);
    }
    aws_promise_release(work->promise);
}

static struct aws_thread s_promise_test_launch_worker(struct promise_test_work *work) {
    const struct aws_thread_options *thread_options = aws_default_thread_options();
    AWS_FATAL_ASSERT(thread_options);
    struct aws_thread worker_thread;
    AWS_FATAL_ASSERT(aws_thread_init(&worker_thread, work->allocator) == AWS_OP_SUCCESS);
    AWS_FATAL_ASSERT(aws_thread_launch(&worker_thread, s_promise_test_worker, work, thread_options) == AWS_OP_SUCCESS);
    return worker_thread;
}

struct pmr_payload {
    struct aws_allocator *allocator;
};

void s_promise_test_free(void *ptr) {
    struct pmr_payload *payload = ptr;
    aws_mem_release(payload->allocator, payload);
}

static int s_promise_test_wait_forever(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_promise *promise = aws_promise_new(allocator);
    ASSERT_NOT_NULL(promise);

    struct pmr_payload *payload = aws_mem_acquire(allocator, 42);
    payload->allocator = allocator;

    struct promise_test_work work = {
        .allocator = allocator,
        .promise = promise,
        .work_time = 2 * 1000 * 1000,
        .value = payload,
        .dtor = s_promise_test_free,
    };
    struct aws_thread worker_thread = s_promise_test_launch_worker(&work);

    aws_promise_wait(promise);
    ASSERT_SUCCESS(aws_thread_join(&worker_thread));
    aws_promise_release(promise);

    return 0;
}

AWS_TEST_CASE(promise_test_wait_forever, s_promise_test_wait_forever)

static int s_promise_test_wait_for_a_bit(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_promise *promise = aws_promise_new(allocator);
    ASSERT_NOT_NULL(promise);

    struct promise_test_work work = {
        .allocator = allocator,
        .promise = promise,
        .work_time = 3 * 1000 * 1000,
    };
    struct aws_thread worker_thread = s_promise_test_launch_worker(&work);
    /* wait until the worker finishes, in 500ms intervals */
    while (!aws_promise_wait_for(promise, 500))
        ;

    ASSERT_TRUE(aws_promise_error_code(promise) == 0);
    ASSERT_NULL(aws_promise_value(promise));

    ASSERT_SUCCESS(aws_thread_join(&worker_thread));
    aws_promise_release(promise);

    return 0;
}

AWS_TEST_CASE(promise_test_wait_for_a_bit, s_promise_test_wait_for_a_bit)

static int s_promise_test_finish_immediately(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_promise *promise = aws_promise_new(allocator);
    ASSERT_NOT_NULL(promise);

    struct promise_test_work work = {
        .allocator = allocator,
        .promise = promise,
        .work_time = 0,
    };
    struct aws_thread worker_thread = s_promise_test_launch_worker(&work);
    aws_promise_wait(promise);
    ASSERT_TRUE(aws_promise_error_code(promise) == 0);
    ASSERT_NULL(aws_promise_value(promise));
    aws_promise_release(promise);
    ASSERT_SUCCESS(aws_thread_join(&worker_thread));

    return 0;
}

AWS_TEST_CASE(promise_test_finish_immediately, s_promise_test_finish_immediately)

static int s_promise_test_finish_before_wait(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_promise *promise = aws_promise_new(allocator);
    ASSERT_NOT_NULL(promise);

    aws_promise_fail(promise, 1024);
    aws_promise_wait(promise);

    ASSERT_TRUE(aws_promise_error_code(promise) == 1024);
    ASSERT_NULL(aws_promise_value(promise));
    aws_promise_release(promise);

    return 0;
}

AWS_TEST_CASE(promise_test_finish_before_wait, s_promise_test_finish_before_wait)

void s_promise_test_waiter(void *data) {
    struct promise_test_work *work = data;
    aws_promise_acquire(work->promise);
    /* sleep 0.2 seconds */
    aws_thread_current_sleep(1000 * 1000 * 2);
    aws_promise_wait(work->promise);
    AWS_FATAL_ASSERT(aws_promise_error_code(work->promise) == 0);
    aws_promise_release(work->promise);
}

static int s_promise_test_multiple_waiters(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_promise *promise = aws_promise_new(allocator);
    ASSERT_NOT_NULL(promise);

    struct promise_test_work work = {
        .allocator = allocator,
        .promise = promise,
        .work_time = 2 * 1000 * 1000,
        .value = promise,
    };
    struct aws_thread threads[8];
    const struct aws_thread_options *worker_options = aws_default_thread_options();
    for (int idx = 0; idx < AWS_ARRAY_SIZE(threads); ++idx) {
        aws_thread_init(&threads[idx], allocator);
        aws_thread_launch(&threads[idx], s_promise_test_waiter, &work, worker_options);
    }

    aws_thread_current_sleep(1000 * 1000 * 4);
    aws_promise_complete(promise, promise, NULL);
    aws_promise_release(promise);

    for (int idx = 0; idx < AWS_ARRAY_SIZE(threads); ++idx) {
        ASSERT_SUCCESS(aws_thread_join(&threads[idx]));
    }

    return 0;
}

AWS_TEST_CASE(promise_test_multiple_waiters, s_promise_test_multiple_waiters)
