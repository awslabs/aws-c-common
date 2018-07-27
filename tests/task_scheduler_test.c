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
#include <aws/common/thread.h>
#include <aws/testing/aws_test_harness.h>

static uint64_t g_timestamp;

static int fake_clock(uint64_t *timestamp) {
    *timestamp = g_timestamp;
    return AWS_OP_SUCCESS;
}

static void set_fake_clock(uint64_t timestamp) {
    g_timestamp = timestamp;
}

static int test_scheduler_ordering(struct aws_allocator *alloc, void *context) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    set_fake_clock(0);

    struct aws_task task2;
    task2.fn = (aws_task_fn *)2;
    task2.arg = (void *)2;

    /* run 250 ms in the future. */
    uint64_t task2_timestamp = 250;
    ASSERT_SUCCESS(
        aws_task_scheduler_schedule_future(&scheduler, &task2, task2_timestamp),
        "Schedule task in %lluns in the future failed",
        task2_timestamp);

    struct aws_task task1;
    task1.fn = (aws_task_fn *)1;
    task1.arg = (void *)1;

    /* run now. */
    ASSERT_SUCCESS(aws_task_scheduler_schedule_now(&scheduler, &task1));

    struct aws_task task3;
    task3.fn = (aws_task_fn *)3;
    task3.arg = (void *)3;

    /* run 500 ms in the future. */
    uint64_t task3_timestamp = 500;
    ASSERT_SUCCESS(
        aws_task_scheduler_schedule_future(&scheduler, &task3, task3_timestamp),
        "Schedule task in %lluns in the future failed.",
        task3_timestamp);

    struct aws_task task_to_run;

    uint64_t timestamp = 0;
    ASSERT_SUCCESS(
        aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp),
        "Task pop on a now() task, should return on the first try");
    ASSERT_INT_EQUALS(
        task2_timestamp,
        timestamp,
        "Timestamp should for next run should be %llu",
        (long long unsigned)task2_timestamp);

    ASSERT_TRUE(task1.fn == task_to_run.fn);
    ASSERT_TRUE(task1.arg == task_to_run.arg);

    set_fake_clock(250);
    ASSERT_SUCCESS(
        aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp), "Task pop should return on the first try");
    ASSERT_INT_EQUALS(
        task3_timestamp,
        timestamp,
        "Timestamp should for next run should be %llu",
        (long long unsigned)task3_timestamp);

    ASSERT_TRUE(task2.fn == task_to_run.fn);
    ASSERT_TRUE(task2.arg == task_to_run.arg);

    set_fake_clock(555);
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp));

    ASSERT_TRUE(task3.fn == task_to_run.fn, );
    ASSERT_TRUE(task3.arg == task_to_run.arg);
    ASSERT_INT_EQUALS(0, timestamp, "When the last task is popped, the timestamp should be 0");

    ASSERT_ERROR(AWS_ERROR_TASK_SCHEDULER_NO_TASKS, aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp));

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static void null_fn(void *arg, enum aws_task_status status) {}

static int test_scheduler_next_task_timestamp(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    set_fake_clock(0);
    struct aws_task task1, task2;
    task1.fn = null_fn;
    task1.arg = (void *)1;
    task2.fn = null_fn;
    task2.arg = (void *)2;

    uint64_t run_at_or_after = 0;
    ASSERT_SUCCESS(
        aws_task_scheduler_schedule_future(&scheduler, &task1, run_at_or_after),
        "Schedule task1 in %lluns in the future failed",
        run_at_or_after);

    run_at_or_after = 10;
    ASSERT_SUCCESS(
        aws_task_scheduler_schedule_future(&scheduler, &task2, run_at_or_after),
        "Schedule task2 in %lluns in the future failed",
        run_at_or_after);

    uint64_t timestamp = 0;
    struct aws_task task_to_run;
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp));
    ASSERT_INT_EQUALS(run_at_or_after, timestamp);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static int test_scheduler_pops_task_fashionably_late(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    set_fake_clock(0);

    struct aws_task task;
    task.fn = (aws_task_fn *)0;
    task.arg = (void *)0;

    uint64_t run_at_or_after = 10;

    ASSERT_SUCCESS(
        aws_task_scheduler_schedule_future(&scheduler, &task, run_at_or_after),
        "Schedule task in %lluns in the future failed",
        run_at_or_after);

    struct aws_task task_to_run = {.fn = 0, .arg = 0};

    uint64_t timestamp = 0;
    ASSERT_FAILS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp));
    int lasterror = aws_last_error();
    ASSERT_INT_EQUALS(AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS, lasterror);
    ASSERT_TRUE(task_to_run.fn == 0, "Popped task should have been null since it is not time for it to run.");
    ASSERT_INT_EQUALS(run_at_or_after, timestamp, "Timestamp should for next run should be %llu", run_at_or_after);

    set_fake_clock(100);
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, 0));

    ASSERT_TRUE(task.fn == task_to_run.fn);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

/* container for running the test making sure a recursive call to aws_task_scheduler_schedule_now
 * does not break the fairness of the task scheduler. */
struct task_scheduler_reentrancy_args {
    struct aws_task_scheduler *scheduler;
    int executed;
    enum aws_task_status status;
    struct task_scheduler_reentrancy_args *next_task_args;
};

static void reentrancy_fn(void *arg, enum aws_task_status status) {

    struct task_scheduler_reentrancy_args *reentrancy_args = (struct task_scheduler_reentrancy_args *)arg;

    if (reentrancy_args->next_task_args) {
        struct aws_task task;
        task.fn = reentrancy_fn;
        task.arg = reentrancy_args->next_task_args;
        aws_task_scheduler_schedule_now(reentrancy_args->scheduler, &task);
    }

    reentrancy_args->executed = 1;
    reentrancy_args->status = status;
}

static int test_scheduler_reentrant_safe(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, aws_high_res_clock_get_ticks);

    struct task_scheduler_reentrancy_args task2_args;
    task2_args.scheduler = &scheduler;
    task2_args.executed = 0;
    task2_args.next_task_args = NULL;

    struct task_scheduler_reentrancy_args task1_args;
    task1_args.scheduler = &scheduler;
    task1_args.executed = 0;
    task1_args.next_task_args = &task2_args;

    struct aws_task task;
    task.arg = &task1_args;
    task.fn = reentrancy_fn;

    ASSERT_SUCCESS(aws_task_scheduler_schedule_now(&scheduler, &task));

    ASSERT_SUCCESS(aws_task_scheduler_run_all(&scheduler, NULL));

    ASSERT_TRUE(task1_args.executed);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task1_args.status);

    ASSERT_FALSE(task2_args.executed);

    ASSERT_SUCCESS(aws_task_scheduler_run_all(&scheduler, NULL));
    ASSERT_TRUE(task2_args.executed);
    ASSERT_INT_EQUALS(AWS_TASK_STATUS_RUN_READY, task2_args.status);

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

struct cancellation_args {
    enum aws_task_status status;
};

static void cancellation_fn(void *arg, enum aws_task_status status) {

    struct cancellation_args *cancellation_args = (struct cancellation_args *)arg;

    cancellation_args->status = status;
}

static int test_scheduler_cleanup_cancellation(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, aws_high_res_clock_get_ticks);

    struct cancellation_args task_args = {.status = 100000};

    struct aws_task task;
    task.arg = &task_args;
    task.fn = cancellation_fn;

    ASSERT_SUCCESS(aws_task_scheduler_schedule_now(&scheduler, &task));
    aws_task_scheduler_clean_up(&scheduler);

    ASSERT_INT_EQUALS(AWS_TASK_STATUS_CANCELED, task_args.status);
    return 0;
}

AWS_TEST_CASE(scheduler_pops_task_late_test, test_scheduler_pops_task_fashionably_late);
AWS_TEST_CASE(scheduler_ordering_test, test_scheduler_ordering);
AWS_TEST_CASE(scheduler_task_timestamp_test, test_scheduler_next_task_timestamp);
AWS_TEST_CASE(scheduler_reentrant_safe, test_scheduler_reentrant_safe);
AWS_TEST_CASE(scheduler_cleanup_cancellation, test_scheduler_cleanup_cancellation);
