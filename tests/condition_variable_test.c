/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/condition_variable.h>

#include <aws/common/clock.h>
#include <aws/common/thread.h>

struct condition_predicate_args {
    int call_count;
};

struct conditional_test_data {
    struct aws_mutex mutex;
    struct aws_condition_variable condition_variable_1;
    struct aws_condition_variable condition_variable_2;
    struct condition_predicate_args *predicate_args;
    int thread_1;
    int thread_2;
    int thread_3;
};

static bool s_conditional_predicate(void *arg) {
    struct condition_predicate_args *condition_predicate_args = (struct condition_predicate_args *)arg;
    condition_predicate_args->call_count++;
    return condition_predicate_args->call_count % 2 == 0;
}

static void s_conditional_thread_2_fn(void *arg) {
    struct conditional_test_data *test_data = (struct conditional_test_data *)arg;

    aws_mutex_lock(&test_data->mutex);

    while (!test_data->thread_1) {
        aws_condition_variable_wait_pred(
            &test_data->condition_variable_1, &test_data->mutex, s_conditional_predicate, test_data->predicate_args);
    }

    test_data->thread_2 = 1;
    aws_condition_variable_notify_one(&test_data->condition_variable_2);
    aws_mutex_unlock(&test_data->mutex);
}

static void s_conditional_thread_3_fn(void *arg) {
    struct conditional_test_data *test_data = (struct conditional_test_data *)arg;

    aws_mutex_lock(&test_data->mutex);

    while (!test_data->thread_1) {
        aws_condition_variable_wait_pred(
            &test_data->condition_variable_1, &test_data->mutex, s_conditional_predicate, test_data->predicate_args);
    }

    test_data->thread_3 = 1;
    aws_condition_variable_notify_one(&test_data->condition_variable_2);
    aws_mutex_unlock(&test_data->mutex);
}

static int s_test_conditional_notify_one_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct condition_predicate_args predicate_args = {.call_count = 0};

    struct conditional_test_data test_data = {
        .condition_variable_1 = AWS_CONDITION_VARIABLE_INIT,
        .condition_variable_2 = AWS_CONDITION_VARIABLE_INIT,
        .mutex = AWS_MUTEX_INIT,
        .predicate_args = &predicate_args,
        .thread_1 = 0,
        .thread_2 = 0,
        .thread_3 = 0,
    };

    ASSERT_SUCCESS(aws_mutex_lock(&test_data.mutex));

    struct aws_thread thread;
    ASSERT_SUCCESS(aws_thread_init(&thread, allocator));
    ASSERT_SUCCESS(aws_thread_launch(&thread, s_conditional_thread_2_fn, &test_data, NULL));

    test_data.thread_1 = 1;
    ASSERT_SUCCESS(aws_condition_variable_notify_one(&test_data.condition_variable_1));

    while (!test_data.thread_2) {
        ASSERT_SUCCESS(aws_condition_variable_wait_pred(
            &test_data.condition_variable_2, &test_data.mutex, s_conditional_predicate, &predicate_args));
    }

    ASSERT_SUCCESS(aws_mutex_unlock(&test_data.mutex));

    aws_thread_join(&thread);
    aws_thread_clean_up(&thread);
    ASSERT_TRUE(predicate_args.call_count >= 2);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(conditional_notify_one, s_test_conditional_notify_one_fn)

static int s_test_conditional_notify_all_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct condition_predicate_args predicate_args = {.call_count = 0};

    struct conditional_test_data test_data = {
        .condition_variable_1 = AWS_CONDITION_VARIABLE_INIT,
        .condition_variable_2 = AWS_CONDITION_VARIABLE_INIT,
        .mutex = AWS_MUTEX_INIT,
        .predicate_args = &predicate_args,
        .thread_1 = 0,
        .thread_2 = 0,
        .thread_3 = 0,
    };

    ASSERT_SUCCESS(aws_mutex_lock(&test_data.mutex));

    struct aws_thread thread_2;
    ASSERT_SUCCESS(aws_thread_init(&thread_2, allocator));
    ASSERT_SUCCESS(aws_thread_launch(&thread_2, s_conditional_thread_2_fn, &test_data, NULL));

    struct aws_thread thread_3;
    ASSERT_SUCCESS(aws_thread_init(&thread_3, allocator));
    ASSERT_SUCCESS(aws_thread_launch(&thread_3, s_conditional_thread_3_fn, &test_data, NULL));

    test_data.thread_1 = 1;
    ASSERT_SUCCESS(aws_condition_variable_notify_all(&test_data.condition_variable_1));

    while (!test_data.thread_2 && !test_data.thread_3) {
        ASSERT_SUCCESS(aws_condition_variable_wait_pred(
            &test_data.condition_variable_2, &test_data.mutex, s_conditional_predicate, &predicate_args));
    }

    ASSERT_SUCCESS(aws_mutex_unlock(&test_data.mutex));

    aws_thread_join(&thread_2);
    aws_thread_join(&thread_3);
    aws_thread_clean_up(&thread_2);
    aws_thread_clean_up(&thread_3);

    ASSERT_TRUE(predicate_args.call_count >= 2);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(conditional_notify_all, s_test_conditional_notify_all_fn)

struct wait_for_max_test_data {
    struct aws_mutex mutex;
    struct aws_condition_variable condition_variable;
    bool done;
};

static bool s_wait_for_max_predicate(void *arg) {
    struct wait_for_max_test_data *test_data = arg;
    return test_data->done;
}

static void s_wait_for_max_thread_fn(void *arg) {
    struct wait_for_max_test_data *test_data = arg;

    aws_thread_current_sleep(aws_timestamp_convert(100, AWS_TIMESTAMP_MILLIS, AWS_TIMESTAMP_NANOS, NULL));

    aws_mutex_lock(&test_data->mutex);
    test_data->done = true;
    aws_condition_variable_notify_one(&test_data->condition_variable);
    aws_mutex_unlock(&test_data->mutex);
}

/* Regression test: with a 32-bit time_t, a huge timeout used to wrap the deadline into the past,
 * so the wait timed out immediately instead of waiting to be notified. */
static int s_test_conditional_wait_for_max_timeout_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct wait_for_max_test_data test_data = {
        .mutex = AWS_MUTEX_INIT,
        .condition_variable = AWS_CONDITION_VARIABLE_INIT,
        .done = false,
    };

    ASSERT_SUCCESS(aws_mutex_lock(&test_data.mutex));

    struct aws_thread thread;
    ASSERT_SUCCESS(aws_thread_init(&thread, allocator));
    ASSERT_SUCCESS(aws_thread_launch(&thread, s_wait_for_max_thread_fn, &test_data, NULL));

    ASSERT_SUCCESS(aws_condition_variable_wait_for_pred(
        &test_data.condition_variable, &test_data.mutex, INT64_MAX, s_wait_for_max_predicate, &test_data));
    ASSERT_TRUE(test_data.done);

    ASSERT_SUCCESS(aws_mutex_unlock(&test_data.mutex));

    aws_thread_join(&thread);
    aws_thread_clean_up(&thread);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(conditional_wait_for_max_timeout, s_test_conditional_wait_for_max_timeout_fn)
