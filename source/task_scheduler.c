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

#include <aws/common/priority_queue.h>
#include <aws/common/thread.h>

#include <assert.h>

static const size_t DEFAULT_QUEUE_SIZE = 7;

struct task_container {
    uint64_t timestamp;
    struct aws_task task;
};

static int s_compare_timestamps(const void *a, const void *b) {
    uint64_t a_time = ((struct task_container *)a)->timestamp;
    uint64_t b_time = ((struct task_container *)b)->timestamp;
    return a_time > b_time; /* min-heap */
}

static inline int s_get_next_task(
    struct aws_task_scheduler *scheduler,
    struct aws_task *task,
    uint64_t run_before,
    uint64_t *next_run_time);

int aws_task_scheduler_init(
    struct aws_task_scheduler *scheduler,
    struct aws_allocator *alloc,
    aws_task_scheduler_clock_fn *clock) {
    scheduler->alloc = alloc;
    scheduler->clock = clock;
    scheduler->min_run_time = 0;
    return aws_priority_queue_init_dynamic(
        &scheduler->queue, alloc, DEFAULT_QUEUE_SIZE, sizeof(struct task_container), &s_compare_timestamps);
}

void aws_task_scheduler_clean_up(struct aws_task_scheduler *scheduler) {
    uint64_t everything_in_past = UINT64_MAX;

    while (1) {
        struct aws_task task_to_run = {0};

        if (s_get_next_task(scheduler, &task_to_run, everything_in_past, NULL)) {
            break;
        }

        assert(task_to_run.fn);
        task_to_run.fn(task_to_run.arg, AWS_TASK_STATUS_CANCELED);
    }

    aws_priority_queue_clean_up(&scheduler->queue);
    scheduler->alloc = NULL;
    scheduler->clock = NULL;
}

static inline int s_get_next_task(
    struct aws_task_scheduler *scheduler,
    struct aws_task *task,
    uint64_t run_before,
    uint64_t *next_run_time) {
    struct task_container *possible_task;
    if (aws_priority_queue_top(&scheduler->queue, (void **)&possible_task)) {
        if (AWS_ERROR_PRIORITY_QUEUE_EMPTY == aws_last_error()) {
            return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_NO_TASKS);
        }
        return AWS_OP_ERR;
    }

    if (next_run_time) {
        *next_run_time = possible_task->timestamp;
    }

    if (possible_task->timestamp > run_before) {
        return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS);
    }

    struct task_container container;
    if (aws_priority_queue_pop(&scheduler->queue, (void *)&container)) {
        return AWS_OP_ERR;
    }

    *task = container.task;
    if (next_run_time) {
        if (aws_priority_queue_top(&scheduler->queue, (void **)&possible_task)) {
            *next_run_time = 0;
            if (AWS_ERROR_PRIORITY_QUEUE_EMPTY == aws_last_error()) {
                return AWS_OP_SUCCESS;
            }
            return AWS_OP_ERR;
        }
        *next_run_time = possible_task->timestamp;
    }
    return AWS_OP_SUCCESS;
}

int aws_task_scheduler_next_task(struct aws_task_scheduler *scheduler, struct aws_task *task, uint64_t *next_run_time) {

    uint64_t now;
    if (scheduler->clock(&now)) {
        return AWS_OP_ERR;
    }

    return s_get_next_task(scheduler, task, now, next_run_time);
}

int aws_task_scheduler_schedule_now(struct aws_task_scheduler *scheduler, struct aws_task *task) {

    uint64_t now;
    if (scheduler->clock(&now)) {
        return AWS_OP_ERR;
    }

    return aws_task_scheduler_schedule_future(scheduler, task, now);
}

int aws_task_scheduler_schedule_future(
    struct aws_task_scheduler *scheduler,
    struct aws_task *task,
    uint64_t time_to_run) {

    struct task_container container;

    /* this serves the purpose of handling reentrant scheduling while the tasks
       are being run. if the clock tick is on the same nanosecond (with
       microsecond precision) as the run was kicked off, it will still be run.
       As a result, if time_to_run is before or on the same clock tick,
       increment it by one nanosecond to avoid the issue. */
    if (AWS_UNLIKELY(time_to_run < scheduler->min_run_time)) {
        time_to_run = scheduler->min_run_time;
    }

    container.task = *task;
    container.timestamp = time_to_run;

    if (aws_priority_queue_push(&scheduler->queue, &container)) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

int aws_task_scheduler_run_all(struct aws_task_scheduler *scheduler, uint64_t *next_task_time) {

    uint64_t now;
    if (scheduler->clock(&now)) {
        return AWS_OP_ERR;
    }

    /* allow mulitple runs in the same clock tick. */
    if (now < scheduler->min_run_time) {
        now = scheduler->min_run_time;
    }

    scheduler->min_run_time = now + 1;

    while (true) {
        struct aws_task task_to_run = {0};

        if (s_get_next_task(scheduler, &task_to_run, now, next_task_time)) {
            int err_code = aws_last_error();
            if (err_code == AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS || err_code == AWS_ERROR_TASK_SCHEDULER_NO_TASKS) {
                return AWS_OP_SUCCESS;
            }

            return AWS_OP_ERR;
        }

        assert(task_to_run.fn);
        task_to_run.fn(task_to_run.arg, AWS_TASK_STATUS_RUN_READY);
    }
}
