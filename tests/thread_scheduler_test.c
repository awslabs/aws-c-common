/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/thread_scheduler.h>

#include <aws/common/clock.h>
#include <aws/common/condition_variable.h>
#include <aws/common/task_scheduler.h>
#include <aws/testing/aws_test_harness.h>

struct executed_task_data {
    struct aws_task *task;
    void *arg;
    enum aws_task_status status;
};

static struct executed_task_data s_executed_tasks[16];
static struct aws_mutex s_test_mutex = AWS_MUTEX_INIT;
static struct aws_condition_variable s_test_c_var = AWS_CONDITION_VARIABLE_INIT;

static size_t s_executed_tasks_n;

/* Updates tl_executed_tasks and tl_executed_task_n when function is executed */
static void s_task_n_fn(struct aws_task *task, void *arg, enum aws_task_status status) {
    AWS_LOGF_INFO(AWS_LS_COMMON_GENERAL, "Invoking task");
    aws_mutex_lock(&s_test_mutex);
    AWS_LOGF_INFO(AWS_LS_COMMON_GENERAL, "Mutex Acquired");
    if (s_executed_tasks_n > AWS_ARRAY_SIZE(s_executed_tasks)) {
        AWS_ASSERT(0);
    }

    struct executed_task_data *data = &s_executed_tasks[s_executed_tasks_n++];
    data->task = task;
    data->arg = arg;
    data->status = status;
    aws_mutex_unlock(&s_test_mutex);
    AWS_LOGF_INFO(AWS_LS_COMMON_GENERAL, "Mutex Released, notifying");

    aws_condition_variable_notify_one(&s_test_c_var);
}

static bool s_scheduled_tasks_ran_predicate(void *arg) {
    size_t *waiting_for = arg;

    return *waiting_for == s_executed_tasks_n;
}

static int s_test_scheduler_ordering(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);
    s_executed_tasks_n = 0;

    struct aws_thread_scheduler *thread_scheduler = aws_thread_scheduler_new(allocator, NULL);
    ASSERT_NOT_NULL(thread_scheduler);

    struct aws_task task2;
    aws_task_init(&task2, s_task_n_fn, (void *)2, "scheduler_ordering_1");

    /* schedule 250 ms in the future. */
    uint64_t task2_timestamp = 0;
    aws_high_res_clock_get_ticks(&task2_timestamp);
    task2_timestamp += 250000000;
    aws_thread_scheduler_schedule_future(thread_scheduler, &task2, task2_timestamp);

    struct aws_task task1;
    aws_task_init(&task1, s_task_n_fn, (void *)1, "scheduler_ordering_2");

    /* schedule now. */
    aws_thread_scheduler_schedule_now(thread_scheduler, &task1);

    struct aws_task task3;
    aws_task_init(&task3, s_task_n_fn, (void *)3, "scheduler_ordering_3");

    /* schedule 500 ms in the future. */
    uint64_t task3_timestamp = 0;
    aws_high_res_clock_get_ticks(&task3_timestamp);
    task3_timestamp += 500000000;
    aws_thread_scheduler_schedule_future(thread_scheduler, &task3, task3_timestamp);
    ASSERT_SUCCESS(aws_mutex_lock(&s_test_mutex));
    size_t expected_runs = 2;
    ASSERT_SUCCESS(aws_condition_variable_wait_pred(
        &s_test_c_var, &s_test_mutex, s_scheduled_tasks_ran_predicate, &expected_runs));

    ASSERT_UINT_EQUALS(2, s_executed_tasks_n);

    struct executed_task_data *task_data = &s_executed_tasks[0];
    ASSERT_PTR_EQUALS(&task1, task_data->task);
    ASSERT_PTR_EQUALS(task1.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    task_data = &s_executed_tasks[1];
    ASSERT_PTR_EQUALS(&task2, task_data->task);
    ASSERT_PTR_EQUALS(task2.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    expected_runs = 3;
    ASSERT_SUCCESS(aws_condition_variable_wait_pred(
        &s_test_c_var, &s_test_mutex, s_scheduled_tasks_ran_predicate, &expected_runs));
    ASSERT_SUCCESS(aws_mutex_unlock(&s_test_mutex));

    /* run task 3 */
    ASSERT_UINT_EQUALS(3, s_executed_tasks_n);

    task_data = &s_executed_tasks[2];
    ASSERT_PTR_EQUALS(&task3, task_data->task);
    ASSERT_PTR_EQUALS(task3.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    aws_thread_scheduler_release(thread_scheduler);
    aws_common_library_clean_up();
    return 0;
}

AWS_TEST_CASE(test_thread_scheduler_ordering, s_test_scheduler_ordering)

static int s_test_scheduler_happy_path_cancellation(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);
    s_executed_tasks_n = 0;

    struct aws_thread_scheduler *thread_scheduler = aws_thread_scheduler_new(allocator, NULL);
    ASSERT_NOT_NULL(thread_scheduler);

    struct aws_task task2;
    aws_task_init(&task2, s_task_n_fn, (void *)2, "scheduler_ordering_1");

    /* schedule 250 ms in the future. */
    uint64_t task2_timestamp = 0;
    aws_high_res_clock_get_ticks(&task2_timestamp);
    task2_timestamp += 250000000;
    aws_thread_scheduler_schedule_future(thread_scheduler, &task2, task2_timestamp);

    struct aws_task task1;
    aws_task_init(&task1, s_task_n_fn, (void *)1, "scheduler_ordering_2");

    /* schedule now. */
    aws_thread_scheduler_schedule_now(thread_scheduler, &task1);

    struct aws_task task3;
    aws_task_init(&task3, s_task_n_fn, (void *)3, "scheduler_ordering_3");

    /* schedule 500 ms in the future. */
    uint64_t task3_timestamp = 0;
    aws_high_res_clock_get_ticks(&task3_timestamp);
    task3_timestamp += 500000000;
    aws_thread_scheduler_schedule_future(thread_scheduler, &task3, task3_timestamp);
    ASSERT_SUCCESS(aws_mutex_lock(&s_test_mutex));
    size_t expected_runs = 2;
    ASSERT_SUCCESS(aws_condition_variable_wait_pred(
        &s_test_c_var, &s_test_mutex, s_scheduled_tasks_ran_predicate, &expected_runs));

    ASSERT_UINT_EQUALS(2, s_executed_tasks_n);

    struct executed_task_data *task_data = &s_executed_tasks[0];
    ASSERT_PTR_EQUALS(&task1, task_data->task);
    ASSERT_PTR_EQUALS(task1.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    task_data = &s_executed_tasks[1];
    ASSERT_PTR_EQUALS(&task2, task_data->task);
    ASSERT_PTR_EQUALS(task2.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    aws_thread_scheduler_cancel_task(thread_scheduler, &task3);
    expected_runs = 3;
    ASSERT_SUCCESS(aws_condition_variable_wait_pred(
        &s_test_c_var, &s_test_mutex, s_scheduled_tasks_ran_predicate, &expected_runs));
    ASSERT_SUCCESS(aws_mutex_unlock(&s_test_mutex));

    /* run task 3 */
    ASSERT_UINT_EQUALS(3, s_executed_tasks_n);

    task_data = &s_executed_tasks[2];
    ASSERT_PTR_EQUALS(&task3, task_data->task);
    ASSERT_PTR_EQUALS(task3.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, task_data->status);

    aws_thread_scheduler_release(thread_scheduler);
    aws_common_library_clean_up();
    return 0;
}

AWS_TEST_CASE(test_thread_scheduler_happy_path_cancellation, s_test_scheduler_happy_path_cancellation)

static struct aws_task s_cancel_task;

static void s_schedule_and_cancel_task(struct aws_task *task, void *arg, enum aws_task_status status) {
    struct aws_thread_scheduler *scheduler = arg;

    aws_task_init(&s_cancel_task, s_task_n_fn, (void *)2, "scheduler_ordering_2");
    aws_thread_scheduler_schedule_now(scheduler, &s_cancel_task);
    aws_thread_scheduler_cancel_task(scheduler, &s_cancel_task);
    s_task_n_fn(task, arg, status);
}

/* schedule a task. Inside that task schedule and then immediately cancel it. This will exercise the pending to be
 * scheduled code path. */
static int s_test_scheduler_cancellation_for_pending_scheduled_task(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);
    s_executed_tasks_n = 0;

    struct aws_thread_scheduler *thread_scheduler = aws_thread_scheduler_new(allocator, NULL);
    ASSERT_NOT_NULL(thread_scheduler);

    struct aws_task task1;
    aws_task_init(&task1, s_schedule_and_cancel_task, thread_scheduler, "scheduler_ordering_1");
    aws_thread_scheduler_schedule_now(thread_scheduler, &task1);

    ASSERT_SUCCESS(aws_mutex_lock(&s_test_mutex));
    size_t expected_runs = 2;
    ASSERT_SUCCESS(aws_condition_variable_wait_pred(
        &s_test_c_var, &s_test_mutex, s_scheduled_tasks_ran_predicate, &expected_runs));

    ASSERT_SUCCESS(aws_mutex_unlock(&s_test_mutex));

    ASSERT_UINT_EQUALS(2, s_executed_tasks_n);

    struct executed_task_data *task_data = &s_executed_tasks[0];
    ASSERT_PTR_EQUALS(&task1, task_data->task);
    ASSERT_PTR_EQUALS(task1.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    task_data = &s_executed_tasks[1];
    ASSERT_PTR_EQUALS(&s_cancel_task, task_data->task);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, task_data->status);

    aws_thread_scheduler_release(thread_scheduler);
    aws_common_library_clean_up();
    return 0;
}

AWS_TEST_CASE(
    test_scheduler_cancellation_for_pending_scheduled_task,
    s_test_scheduler_cancellation_for_pending_scheduled_task)
