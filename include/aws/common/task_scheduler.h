#ifndef AWS_TASK_SCHEDULER_H
#define AWS_TASK_SCHEDULER_H

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
#include <aws/common/priority_queue.h>
#include <stdint.h>


/**
 * Pointer to the scheduled function
 */
typedef void(*aws_task_fn)(void *arg);

/**
 * Monotonic clock function
 */
typedef int(*aws_task_scheduler_clock)(uint64_t *);

struct aws_task {
    aws_task_fn fn;
    void *arg;
};

struct aws_task_scheduler {
    struct aws_allocator *alloc;
    struct aws_priority_queue queue;
    uint64_t owning_thread;
    aws_task_scheduler_clock clock;
};

#ifdef __cplusplus
extern "C" {
#endif

    /**
     * Initializes a task scheduler instance with a clock function and an allocator.
     * The recommended clock functions are in <aws/common/clock.h>
     *
     * Note: This needs to be called from the thread that will own the scheduler. Cross-thread access is not allowed 
     * and will always raise AWS_ERROR_TASK_SCHEDULER_ILLEGAL_XTHREAD_ACCESS error.
     */
    AWS_COMMON_API int aws_task_scheduler_init(struct aws_task_scheduler *scheduler, 
            struct aws_allocator *alloc, aws_task_scheduler_clock clock);

    /**
     * Cleans up any memory allocated, and prepares the instance for reuse or deletion.
     */
    AWS_COMMON_API void aws_task_scheduler_clean_up(struct aws_task_scheduler *scheduler);

    /**
     * Gets the next task that is ready for execution. Tasks in the future will not be returned, 
     * even if they are the highest priority. next_run_time, if it is not null, and there are any tasks scheduled
     * will be set to the timestamp for the highest priority task. This is a useful hint for setting timeouts on
     * event loops, or thread sleeps. If no tasks are scheduled, this value will be set to -1.
     * If no tasks are ready for execution AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS error will be raised.
     *
     * If no tasks are scheduled AWS_ERROR_TASK_SCHEDULER_NO_TASKS error will be raised.
     * task is copied.
     */
    AWS_COMMON_API int aws_task_scheduler_next_task(struct aws_task_scheduler *scheduler, struct aws_task *task, 
            uint64_t *next_run_time);

    /**
     * Schedules a task to run immediately. task is copied
     */
    AWS_COMMON_API int aws_task_scheduler_schedule_now(struct aws_task_scheduler *queue, struct aws_task *task);

    /**
     * Schedules a task to run at time_to_run units after the current time. task is copied
     */
    AWS_COMMON_API int aws_task_scheduler_schedule_future(struct aws_task_scheduler *queue, struct aws_task *task, 
            uint64_t time_to_run);

    /**
     * Sequentially execute all tasks that are ready until either the queue is empty or no ready tasks are available.
     * next_task_time is the time in nanoseconds (based on the configured aws_task_scheduler_clock) when the
     * next task will be ready for execution.
     *
     * This function protects against reentrancy by pegging the comparision timestamp before checking the queue,
     * therefore if a task schedules another task, it will not be executed until the next call to this function.
     *
     * Differently than the aws_task_scheduler_next_task() fn, this function will return AWS_OP_SUCCESS even if
     * no tasks are scheduled. AWS_OP_ERR is only returned if an actual error condition occurs (OOM, Clock failure etc...).
     */
    AWS_COMMON_API int aws_task_scheduler_run_all(struct aws_task_scheduler *queue, uint64_t *next_task_time);

#ifdef __cplusplus
}
#endif

#endif /* #ifndef AWS_PRIORITY_QUEUE_H */
