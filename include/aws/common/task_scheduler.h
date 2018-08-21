#ifndef AWS_COMMON_TASK_SCHEDULER_H
#define AWS_COMMON_TASK_SCHEDULER_H

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

#include <aws/common/common.h>
#include <aws/common/linked_list.h>
#include <aws/common/priority_queue.h>

struct aws_task;

typedef enum aws_task_status {
    AWS_TASK_STATUS_RUN_READY,
    AWS_TASK_STATUS_CANCELED,
} aws_task_status;

/**
 * A scheduled function.
 */
typedef void(aws_task_fn)(struct aws_task *task, void *arg, enum aws_task_status);

/*
 * A task object.
 * Once added to the scheduler, a task must remain in memory until its function is executed.
 */
struct aws_task {
    aws_task_fn *fn;
    void *arg;
    uint64_t timestamp;
    struct aws_linked_list_node node;
};

static inline void aws_task_init(struct aws_task *task, aws_task_fn *fn, void *arg) {
    task->fn = fn;
    task->arg = arg;
    task->timestamp = 0;
    aws_linked_list_node_reset(&task->node);
}

struct aws_task_scheduler {
    struct aws_allocator *alloc;
    struct aws_priority_queue timed_queue; /* Tasks scheduled to run at specific times */
    struct aws_linked_list asap_list;      /* Tasks scheduled to run as soon as possible */
    struct aws_linked_list running_list;   /* Tasks currently being executed */
};

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes a task scheduler instance.
 */
AWS_COMMON_API
int aws_task_scheduler_init(struct aws_task_scheduler *scheduler, struct aws_allocator *alloc);

/**
 * Empties and executes all queued tasks, passing the AWS_TASK_STATUS_CANCELED status to the task function.
 * Cleans up any memory allocated, and prepares the instance for reuse or deletion.
 */
AWS_COMMON_API
void aws_task_scheduler_clean_up(struct aws_task_scheduler *scheduler);

/**
 * Returns whether the scheduler has any scheduled tasks.
 * next_task_time (optional) will be set to time of the next task, note that 0 will be set if tasks were
 * added via aws_task_scheduler_schedule_now() and UINT64_MAX will be set if no tasks are scheduled at all.
 */
AWS_COMMON_API
bool aws_task_scheduler_has_tasks(const struct aws_task_scheduler *scheduler, uint64_t *out_next_task_time);


/**
 * Schedules a task to run immediately.
 * The task should not be cleaned up or modified until its function is executed.
 */
AWS_COMMON_API
void aws_task_scheduler_schedule_now(struct aws_task_scheduler *scheduler, struct aws_task *task);

/**
 * Schedules a task to run at time_to_run units after the current time.
 * The task should not be cleaned up or modified until its function is executed.
 */
AWS_COMMON_API
int aws_task_scheduler_schedule_future(
    struct aws_task_scheduler *scheduler,
    struct aws_task *task,
    uint64_t time_to_run);

/**
 * Sequentially execute all tasks scheduled to run at, or before current_time.
 * AWS_TASK_STATUS_RUN_READY will be passed to the task function as the task status.
 *
 * If a task schedules another task, the new task will not be executed until the next call to this function.
 */
AWS_COMMON_API
void aws_task_scheduler_run_all(struct aws_task_scheduler *scheduler, uint64_t current_time);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_TASK_SCHEDULER_H */
