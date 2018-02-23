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
    task2.fn = (aws_task_fn)2;
    task2.arg = (void *)2;

    /* run 250 ms in the future. */
    uint64_t task2_timestamp = 250;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task2, task2_timestamp),
                   "Schedule task in %lluns in the future failed", task2_timestamp);

    struct aws_task task1;
    task1.fn = (aws_task_fn)1;
    task1.arg = (void *)1;

    /* run now. */
    ASSERT_SUCCESS(aws_task_scheduler_schedule_now(&scheduler, &task1), "Failed to schedule task1");

    struct aws_task task3;
    task3.fn = (aws_task_fn)3;
    task3.arg = (void *)3;

    /* run 500 ms in the future. */
    uint64_t task3_timestamp = 500;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task3, task3_timestamp),
                   "Schedule task in %lluns in the future failed.", task3_timestamp);

    struct aws_task task_to_run;

    uint64_t timestamp = 0;
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp),
                   "Task pop on a now() task, should return on the first try");
    ASSERT_INT_EQUALS(task2_timestamp, timestamp, "Timestamp should for next run should be %llu",
                      (long long unsigned)task2_timestamp);

    ASSERT_TRUE(task1.fn == task_to_run.fn, "Popped task should have been task 1.");
    ASSERT_TRUE(task1.arg == task_to_run.arg, "Popped task arg should have been task 1.");

    set_fake_clock(250);
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp),
                   "Task pop should return on the first try");
    ASSERT_INT_EQUALS(task3_timestamp, timestamp, "Timestamp should for next run should be %llu",
                      (long long unsigned)task3_timestamp);

    ASSERT_TRUE(task2.fn == task_to_run.fn, "Popped task should have been task 2.");
    ASSERT_TRUE(task2.arg == task_to_run.arg, "Popped task arg should have been task 2.");

    set_fake_clock(555);
    int err = aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp);
    ASSERT_FAILS(err, "scheduler should return error code when no more tasks are available");
    ASSERT_INT_EQUALS(AWS_ERROR_TASK_SCHEDULER_NO_MORE_TASKS, aws_last_error(),
                      "scheduler returned unexpected error code");

    ASSERT_TRUE(task3.fn == task_to_run.fn, "Popped task should have been task 3.");
    ASSERT_TRUE(task3.arg == task_to_run.arg, "Popped task arg should have been task 3.");

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static int test_scheduler_next_task_timestamp(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    set_fake_clock(0);
    struct aws_task task1, task2;
    task1.fn = (aws_task_fn)1;
    task1.arg = (void *)1;
    task2.fn = (aws_task_fn)2;
    task2.arg = (void *)2;

    uint64_t run_at_or_after = 0;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task1, run_at_or_after),
                   "Schedule task1 in %lluns in the future failed", run_at_or_after);

    run_at_or_after = 10;
    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task2, run_at_or_after),
                   "Schedule task2 in %lluns in the future failed", run_at_or_after);

    uint64_t timestamp = 0;
    struct aws_task task_to_run;
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp), "Next task returned error");
    ASSERT_INT_EQUALS(run_at_or_after, timestamp, "Timestamp of next task ready time does not match");

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

static int test_scheduler_pops_task_fashionably_late(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    set_fake_clock(0);

    struct aws_task task;
    task.fn = (aws_task_fn)0;
    task.arg = (void *)0;

    uint64_t run_at_or_after = 10;

    ASSERT_SUCCESS(aws_task_scheduler_schedule_future(&scheduler, &task, run_at_or_after),
                   "Schedule task in %lluns in the future failed", run_at_or_after);

    struct aws_task task_to_run = {.fn = 0, .arg = 0};

    uint64_t timestamp = 0;
    ASSERT_FAILS(aws_task_scheduler_next_task(&scheduler, &task_to_run, &timestamp),
                 "Next task should have returned error");
    int lasterror = aws_last_error();
    ASSERT_INT_EQUALS(AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS, lasterror, "Status should be no ready tasks.");
    ASSERT_TRUE(task_to_run.fn == 0, "Popped task should have been null since it is not time for it to run.");
    ASSERT_INT_EQUALS(run_at_or_after, timestamp, "Timestamp should for next run should be %llu", run_at_or_after);

    set_fake_clock(100);
    ASSERT_SUCCESS(aws_task_scheduler_next_task(&scheduler, &task_to_run, 0), "Next task should have succeeded.");

    ASSERT_TRUE(task.fn == task_to_run.fn, "Popped task should have been task.");

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

struct task_scheduler_thread_args {
    struct aws_task_scheduler *scheduler;
    int schedule_ret_val;
    int pop_ret_val;
};

static void task_scheduler_thread_fn(void *arg) {
    struct aws_task task;
    task.fn = 0;
    task.arg = 0;

    struct task_scheduler_thread_args *thread_args = (struct task_scheduler_thread_args *)arg;
    aws_task_scheduler_schedule_now(thread_args->scheduler, &task);
    thread_args->schedule_ret_val = aws_last_error();

    struct aws_task task_to_run;
    aws_task_scheduler_next_task(thread_args->scheduler, &task_to_run, 0);
    thread_args->pop_ret_val = aws_last_error();
}

static int test_scheduler_rejects_xthread_access(struct aws_allocator *alloc, void *ctx) {
    struct aws_task_scheduler scheduler;
    aws_task_scheduler_init(&scheduler, alloc, fake_clock);

    struct aws_thread thread;
    aws_thread_init(&thread, alloc);

    struct task_scheduler_thread_args thread_args;
    thread_args.scheduler = &scheduler;
    thread_args.pop_ret_val = 0;
    thread_args.schedule_ret_val = 0;

    aws_thread_launch(&thread, &task_scheduler_thread_fn, &thread_args, 0);
    aws_thread_join(&thread);
    aws_thread_clean_up(&thread);

    ASSERT_INT_EQUALS(AWS_ERROR_TASK_SCHEDULER_ILLEGAL_XTHREAD_ACCESS, thread_args.schedule_ret_val,
                      "Another thread should not have been able to mutate the scheduler.");

    ASSERT_INT_EQUALS(AWS_ERROR_TASK_SCHEDULER_ILLEGAL_XTHREAD_ACCESS, thread_args.pop_ret_val,
                      "Another thread should not have been able to mutate the scheduler.");

    aws_task_scheduler_clean_up(&scheduler);
    return 0;
}

AWS_TEST_CASE(scheduler_rejects_xthread_access_test, test_scheduler_rejects_xthread_access);
AWS_TEST_CASE(scheduler_pops_task_late_test, test_scheduler_pops_task_fashionably_late);
AWS_TEST_CASE(scheduler_ordering_test, test_scheduler_ordering);
AWS_TEST_CASE(scheduler_task_timestamp_test, test_scheduler_next_task_timestamp);
