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

#include <aws/common/task_scheduler.h>
#include <aws/testing/aws_test_harness.h>

struct executed_task_data {
    struct aws_task *task;
    void *arg;
    enum aws_task_status status;
};

static AWS_THREAD_LOCAL struct executed_task_data tl_executed_tasks[16];

static AWS_THREAD_LOCAL size_t tl_executed_tasks_n;

/* Updates tl_executed_tasks and tl_executed_task_n when function is executed */
void task_n_fn(struct aws_task *task, void *arg, enum aws_task_status status) {
    if (tl_executed_tasks_n > AWS_ARRAY_SIZE(tl_executed_tasks)) {
        assert(0);
    }

    struct executed_task_data *data = &tl_executed_tasks[tl_executed_tasks_n++];
    data->task = task;
    data->arg = arg;
    data->status = status;
}

static int test_scheduler_ordering(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    tl_executed_tasks_n = 0;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    struct aws_task task2;
    aws_task_init(&task2, task_n_fn, (void *)2);

    /* schedule 250 ns in the future. */
    uint64_t task2_timestamp = 250;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task2, task2_timestamp));

    struct aws_task task1;
    aws_task_init(&task1, task_n_fn, (void *)1);

    /* schedule now. */
    aws_task_scheduler_schedule_now(&scheduler, &task1);

    struct aws_task task3;
    aws_task_init(&task3, task_n_fn, (void *)3);

    /* schedule 500 ns in the future. */
    uint64_t task3_timestamp = 500;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task3, task3_timestamp));

    /* run tasks 1 and 2 (but not 3) */
    aws_task_scheduler_run_all(&scheduler, task2_timestamp);

    ASSERT_UINT_EQUALS(2, tl_executed_tasks_n);

    struct executed_task_data *task_data = &tl_executed_tasks[0];
    ASSERT_PTR_EQUALS(&task1, task_data->task);
    ASSERT_PTR_EQUALS(task1.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    task_data = &tl_executed_tasks[1];
    ASSERT_PTR_EQUALS(&task2, task_data->task);
    ASSERT_PTR_EQUALS(task2.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    /* run task 3 */
    aws_task_scheduler_run_all(&scheduler, task3.timestamp);

    ASSERT_UINT_EQUALS(3, tl_executed_tasks_n);

    task_data = &tl_executed_tasks[2];
    ASSERT_PTR_EQUALS(&task3, task_data->task);
    ASSERT_PTR_EQUALS(task3.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static void s_null_fn(struct aws_task *task, void *arg, enum aws_task_status status) {
    (void)task;
    (void)arg;
    (void)status;
}

static int test_scheduler_has_tasks(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    /* Check when no tasks scheduled */
    uint64_t next_task_time = 123456;
    ASSERT_FALSE(aws_task_scheduler_has_tasks(&scheduler, &next_task_time));
    ASSERT_UINT_EQUALS(UINT64_MAX, next_task_time);

    /* Check when a task is scheduled for the future */
    struct aws_task timed_task;
    aws_task_init(&timed_task, s_null_fn, (void *)1);

    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &timed_task, 10));
    ASSERT_TRUE(aws_task_scheduler_has_tasks(&scheduler, &next_task_time));
    ASSERT_UINT_EQUALS(10, next_task_time);

    /* Check when a task is scheduled for now */
    struct aws_task now_task;
    aws_task_init(&now_task, s_null_fn, (void *)2);

    aws_task_scheduler_schedule_now(&scheduler, &now_task);
    ASSERT_TRUE(aws_task_scheduler_has_tasks(&scheduler, &next_task_time));
    ASSERT_UINT_EQUALS(0, next_task_time);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static int test_scheduler_pops_task_fashionably_late(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    tl_executed_tasks_n = 0;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    struct aws_task task;
    aws_task_init(&task, task_n_fn, (void *)0);

    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task, 10));

    /* Run scheduler before task is supposed to execute, check that it didn't execute */
    aws_task_scheduler_run_all(&scheduler, 5);

    ASSERT_UINT_EQUALS(0, tl_executed_tasks_n);

    /* Run scheduler long after task was due to execute, check that it executed */
    aws_task_scheduler_run_all(&scheduler, 500);
    ASSERT_UINT_EQUALS(1, tl_executed_tasks_n);

    struct executed_task_data *task_data = &tl_executed_tasks[0];
    ASSERT_PTR_EQUALS(&task, task_data->task);
    ASSERT_PTR_EQUALS(task.arg, task_data->arg);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task_data->status);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

/* container for running a task that schedules another task when it executes */
struct task_scheduler_reentrancy_args {
    struct aws_task_scheduler *scheduler;
    struct aws_task task;
    bool executed;
    enum aws_task_status status;
    struct task_scheduler_reentrancy_args *next_task_args;
};

static void s_reentrancy_fn(struct aws_task *task, void *arg, enum aws_task_status status) {
    (void *)task;
    struct task_scheduler_reentrancy_args *reentrancy_args = (struct task_scheduler_reentrancy_args *)arg;

    if (reentrancy_args->next_task_args) {
        aws_task_scheduler_schedule_now(reentrancy_args->scheduler, &reentrancy_args->next_task_args->task);
    }

    reentrancy_args->executed = 1;
    reentrancy_args->status = status;
}

static void s_reentrancy_args_init(struct task_scheduler_reentrancy_args *args, struct aws_task_scheduler *scheduler, struct task_scheduler_reentrancy_args *next_task_args) {
    AWS_ZERO_STRUCT(*args);
    args->scheduler = scheduler;
    aws_task_init(&args->task, s_reentrancy_fn, args);
    args->status = (enum aws_task_status)-1;
    args->next_task_args = next_task_args;
}

static int test_scheduler_reentrant_safe(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    /* When task1 executes, it schedules task2 */
    struct task_scheduler_reentrancy_args task2_args;
    s_reentrancy_args_init(&task2_args, &scheduler, NULL);

    struct task_scheduler_reentrancy_args task1_args;
    s_reentrancy_args_init(&task1_args, &scheduler, &task2_args);

    aws_task_scheduler_schedule_now(&scheduler, &task1_args.task);

    /* Run, only task1 should have executed */
    aws_task_scheduler_run_all(&scheduler, 100);

    ASSERT_TRUE(task1_args.executed);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task1_args.status);

    ASSERT_FALSE(task2_args.executed);

    /* Run again, task2 should execute */
    aws_task_scheduler_run_all(&scheduler, 200);
    
    ASSERT_TRUE(task2_args.executed);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task2_args.status);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

struct cancellation_args {
    enum aws_task_status status;
};

static void cancellation_fn(struct aws_task *task, void *arg, enum aws_task_status status) {

    (void)task;
    struct cancellation_args *cancellation_args = (struct cancellation_args *)arg;

    cancellation_args->status = status;
}

static int test_scheduler_cleanup_cancellation(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    struct cancellation_args now_task_args = {.status = 100000};
    struct aws_task now_task;
    aws_task_init(&now_task, cancellation_fn, &now_task_args);
    aws_task_scheduler_schedule_now(&scheduler, &now_task);

    struct cancellation_args future_task_args = {.status = 100000};
    struct aws_task future_task;
    aws_task_init(&future_task, cancellation_fn, &future_task_args);
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &future_task, 9999999999999));

    aws_task_scheduler_clean_up(&scheduler);

    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, now_task_args.status);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, future_task_args.status);
    return 0;
}

static int test_scheduler_cleanup_reentrants(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, allocator);

    /* When now_task1 executes, it schedules now_task2 */
    struct task_scheduler_reentrancy_args now_task2_args;
    s_reentrancy_args_init(&now_task2_args, &scheduler, NULL);

    struct task_scheduler_reentrancy_args now_task1_args;
    s_reentrancy_args_init(&now_task1_args, &scheduler, &now_task2_args);

    aws_task_scheduler_schedule_now(&scheduler, &now_task1_args.task);

    /* When future_task1 executes, it schedules future_task2 */
    struct task_scheduler_reentrancy_args future_task2_args;
    s_reentrancy_args_init(&future_task2_args, &scheduler, NULL);
    
    struct task_scheduler_reentrancy_args future_task1_args;
    s_reentrancy_args_init(&future_task1_args, &scheduler, &future_task2_args);
    
    aws_task_scheduler_schedule_future(&scheduler, &future_task1_args.task, 555555555555555555);

    /* Clean up scheduler. All tasks should be executed with CANCELLED status */
    aws_task_scheduler_clean_up(&scheduler);

    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, now_task1_args.status);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, now_task2_args.status);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, future_task1_args.status);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, future_task2_args.status);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(scheduler_pops_task_late_test, test_scheduler_pops_task_fashionably_late);
AWS_TEST_CASE(scheduler_ordering_test, test_scheduler_ordering);
AWS_TEST_CASE(scheduler_has_tasks_test, test_scheduler_has_tasks);
AWS_TEST_CASE(scheduler_reentrant_safe, test_scheduler_reentrant_safe);
AWS_TEST_CASE(scheduler_cleanup_cancellation, test_scheduler_cleanup_cancellation);
AWS_TEST_CASE(scheduler_cleanup_reentrants, test_scheduler_cleanup_reentrants);
