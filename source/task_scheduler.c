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
#include <aws/common/priority_queue.h>

static const size_t DEFAULT_QUEUE_SIZE = 7;

struct task_container {
    uint64_t timestamp;
    struct aws_task task;
};

static int compare_timestamps(const void *a, const void *b) {
    uint64_t a_time = ((struct task_container*)a)->timestamp;
    uint64_t b_time = ((struct task_container*)b)->timestamp;
    return a_time > b_time; /* min-heap */
}

int aws_task_scheduler_init(struct aws_task_scheduler *scheduler, struct aws_allocator *alloc, 
        aws_task_scheduler_clock clock) {
    scheduler->alloc = alloc;
    scheduler->clock = clock;
    scheduler->owning_thread = aws_thread_current_thread_id();
    return aws_priority_queue_dynamic_init(&scheduler->queue, alloc, DEFAULT_QUEUE_SIZE, sizeof(struct task_container), 
            &compare_timestamps);
}

void aws_task_scheduler_clean_up(struct aws_task_scheduler *scheduler) {
     /* do we want to add a xthread check here? what happens if another thread attempts to clean up? */
    aws_priority_queue_clean_up(&scheduler->queue);
    scheduler->alloc = NULL;
    scheduler->clock = NULL;
    scheduler->owning_thread = 0;
}

int aws_task_scheduler_next_task(struct aws_task_scheduler *scheduler, 
        struct aws_task *task, uint64_t *next_run_time) {

    if (aws_thread_current_thread_id() != scheduler->owning_thread) {
        return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_ILLEGAL_XTHREAD_ACCESS);
    }

    struct task_container *possible_task;
    if(aws_priority_queue_top(&scheduler->queue, (void **)&possible_task)) {
        if(AWS_ERROR_PRIORITY_QUEUE_EMPTY == aws_last_error()) {
            return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_NO_TASKS);
        }
        return AWS_OP_ERR;
    }

    if (next_run_time) {
        *next_run_time = possible_task->timestamp;
    }

    uint64_t now;
    if(scheduler->clock(&now)) {
        return AWS_OP_ERR;
    }

    if (possible_task->timestamp > now) {
        return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS);
    }

    struct task_container container;
    if(aws_priority_queue_pop(&scheduler->queue, (void *)&container)) {
        return AWS_OP_ERR;
    }

    *task = container.task;
    if(next_run_time) {
        if(aws_priority_queue_top(&scheduler->queue, (void **)&possible_task)) {
            if(AWS_ERROR_PRIORITY_QUEUE_EMPTY == aws_last_error()) {
                return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_NO_MORE_TASKS);
            }
            return AWS_OP_ERR;
        }
        *next_run_time = possible_task->timestamp;
    }
    return AWS_OP_SUCCESS;
}

int aws_task_scheduler_schedule_now(struct aws_task_scheduler *scheduler,
        struct aws_task *task) {

    uint64_t now;
    if(scheduler->clock(&now)) {
        return AWS_OP_ERR;
    }
    return aws_task_scheduler_schedule_future(scheduler, task, now);
}

int aws_task_scheduler_schedule_future(struct aws_task_scheduler *scheduler, 
        struct aws_task *task, uint64_t time_to_run) {

    if (aws_thread_current_thread_id() != scheduler->owning_thread) {
        return aws_raise_error(AWS_ERROR_TASK_SCHEDULER_ILLEGAL_XTHREAD_ACCESS);
    }

    struct task_container container;

    container.task = *task;
    container.timestamp = time_to_run;

    if(aws_priority_queue_push(&scheduler->queue, &container)) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

int aws_task_scheduler_run_all(struct aws_task_scheduler *scheduler) {
    while(1) {
        struct aws_task task_to_run = {0};
        int err = aws_task_scheduler_next_task(scheduler, &task_to_run, 0);
        if(AWS_OP_SUCCESS != err) {
            return err;
        }
        task_to_run.fn(task_to_run.arg);
    }
    return AWS_OP_SUCCESS;
}
