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

#include <assert.h>

static const size_t DEFAULT_QUEUE_SIZE = 7;

static int s_compare_timestamps(const void *a, const void *b) {
    uint64_t a_time = (*(struct aws_task **)a)->timestamp;
    uint64_t b_time = (*(struct aws_task **)b)->timestamp;
    return a_time > b_time; /* min-heap */
}

static void s_run_all(struct aws_task_scheduler *scheduler, uint64_t current_time, enum aws_task_status status);

int aws_task_scheduler_init(struct aws_task_scheduler *scheduler, struct aws_allocator *alloc) {
    assert(alloc);

    scheduler->alloc = alloc;
    aws_linked_list_init(&scheduler->timed_list);
    aws_linked_list_init(&scheduler->asap_list);
    return aws_priority_queue_init_dynamic(
        &scheduler->timed_queue, alloc, DEFAULT_QUEUE_SIZE, sizeof(struct aws_task *), &s_compare_timestamps);
}

void aws_task_scheduler_clean_up(struct aws_task_scheduler *scheduler) {
    assert(scheduler);

    /* Execute all remaining tasks as CANCELED.
     * Do this in a loop so that tasks scheduled by other tasks are executed */
    while (aws_task_scheduler_has_tasks(scheduler, NULL)) {
        s_run_all(scheduler, UINT64_MAX, AWS_TASK_STATUS_CANCELED);
    }

    aws_priority_queue_clean_up(&scheduler->timed_queue);
    AWS_ZERO_STRUCT(scheduler);
}

bool aws_task_scheduler_has_tasks(const struct aws_task_scheduler *scheduler, uint64_t *next_task_time) {
    assert(scheduler);

    uint64_t timestamp = UINT64_MAX;
    bool has_tasks = false;

    if (!aws_linked_list_empty(&scheduler->asap_list)) {
        timestamp = 0;
        has_tasks = true;

    } else {
        /* Check whether timed_list or timed_queue has the earlier task */
        if (AWS_UNLIKELY(!aws_linked_list_empty(&scheduler->timed_list))) {
            struct aws_linked_list_node *node = aws_linked_list_front(&scheduler->timed_list);
            struct aws_task *task = AWS_CONTAINER_OF(node, struct aws_task, node);
            timestamp = task->timestamp;
            has_tasks = true;
        }

        struct aws_task **task_ptrptr = NULL;
        if (aws_priority_queue_top(&scheduler->timed_queue, (void **)&task_ptrptr) == AWS_OP_SUCCESS) {
            if ((*task_ptrptr)->timestamp < timestamp) {
                timestamp = (*task_ptrptr)->timestamp;
            }
            has_tasks = true;
        }
    }

    if (next_task_time) {
        *next_task_time = timestamp;
    }
    return has_tasks;
}

void aws_task_scheduler_schedule_now(struct aws_task_scheduler *scheduler, struct aws_task *task) {
    assert(scheduler);
    assert(task);
    assert(task->fn);

    task->priority_queue_node.current_index = SIZE_MAX;
    aws_linked_list_node_reset(&task->node);
    task->timestamp = 0;

    aws_linked_list_push_back(&scheduler->asap_list, &task->node);
}

void aws_task_scheduler_schedule_future(
    struct aws_task_scheduler *scheduler,
    struct aws_task *task,
    uint64_t time_to_run) {

    assert(scheduler);
    assert(task);
    assert(task->fn);

    task->timestamp = time_to_run;

    task->priority_queue_node.current_index = SIZE_MAX;
    aws_linked_list_node_reset(&task->node);
    int err = aws_priority_queue_push_ref(&scheduler->timed_queue, &task, &task->priority_queue_node);
    if (AWS_UNLIKELY(err)) {
        /* In the (very unlikely) case that we can't push into the timed_queue,
         * perform a sorted insertion into timed_list. */
        struct aws_linked_list_node *node_i;
        for (node_i = aws_linked_list_begin(&scheduler->timed_list);
             node_i != aws_linked_list_end(&scheduler->timed_list);
             node_i = aws_linked_list_next(node_i)) {

            struct aws_task *task_i = AWS_CONTAINER_OF(node_i, struct aws_task, node);
            if (task_i->timestamp > time_to_run) {
                break;
            }
        }
        aws_linked_list_insert_before(node_i, &task->node);
    }
}

void aws_task_scheduler_run_all(struct aws_task_scheduler *scheduler, uint64_t current_time) {
    assert(scheduler);

    s_run_all(scheduler, current_time, AWS_TASK_STATUS_RUN_READY);
}

static void s_run_all(struct aws_task_scheduler *scheduler, uint64_t current_time, enum aws_task_status status) {

    /* Move scheduled tasks to running_list before executing.
     * This gives us the desired behavior that: if executing a task results in another task being scheduled,
     * that new task is not executed until the next time run() is invoked. */
    struct aws_linked_list running_list;
    aws_linked_list_init(&running_list);

    /* First move everything from asap_list */
    aws_linked_list_swap_contents(&running_list, &scheduler->asap_list);

    /* Next move tasks from timed_queue and timed_list, based on whichever's next-task is sooner.
     * It's very unlikely that any tasks are in timed_list, so once it has no more valid tasks,
     * break out of this complex loop in favor of a simpler one. */
    while (AWS_UNLIKELY(!aws_linked_list_empty(&scheduler->timed_list))) {

        struct aws_linked_list_node *timed_list_node = aws_linked_list_begin(&scheduler->timed_list);
        struct aws_task *timed_list_task = AWS_CONTAINER_OF(timed_list_node, struct aws_task, node);
        if (timed_list_task->timestamp > current_time) {
            /* timed_list is out of valid tasks, break out of complex loop */
            break;
        }

        /* Check if timed_queue has a task which is sooner */
        struct aws_task **timed_queue_task_ptrptr = NULL;
        if (aws_priority_queue_top(&scheduler->timed_queue, (void **)&timed_queue_task_ptrptr) == AWS_OP_SUCCESS) {
            if ((*timed_queue_task_ptrptr)->timestamp <= current_time) {
                if ((*timed_queue_task_ptrptr)->timestamp < timed_list_task->timestamp) {
                    /* Take task from timed_queue */
                    struct aws_task *timed_queue_task;
                    aws_priority_queue_pop(&scheduler->timed_queue, &timed_queue_task);
                    aws_linked_list_push_back(&running_list, &timed_queue_task->node);
                    continue;
                }
            }
        }

        /* Take task from timed_list */
        aws_linked_list_pop_front(&scheduler->timed_list);
        aws_linked_list_push_back(&running_list, &timed_list_task->node);
    }

    /* Simpler loop that moves remaining valid tasks from timed_queue */
    struct aws_task **timed_queue_task_ptrptr = NULL;
    while (aws_priority_queue_top(&scheduler->timed_queue, (void **)&timed_queue_task_ptrptr) == AWS_OP_SUCCESS) {
        if ((*timed_queue_task_ptrptr)->timestamp > current_time) {
            break;
        }

        struct aws_task *next_timed_task;
        aws_priority_queue_pop(&scheduler->timed_queue, &next_timed_task);
        aws_linked_list_push_back(&running_list, &next_timed_task->node);
    }

    /* Run tasks */
    while (!aws_linked_list_empty(&running_list)) {
        struct aws_linked_list_node *task_node = aws_linked_list_pop_front(&running_list);
        struct aws_task *task = AWS_CONTAINER_OF(task_node, struct aws_task, node);
        aws_task_run(task, status);
    }
}

void aws_task_scheduler_cancel_task(struct aws_task_scheduler *scheduler, struct aws_task *task) {
    /* attempt the linked lists first since those will be faster access and more likely to occur
     * anyways.
     */
    if (task->node.next) {
        aws_linked_list_remove(&task->node);
    } else {
        aws_priority_queue_remove(&scheduler->timed_queue, &task, &task->priority_queue_node);
    }
    aws_task_run(task, AWS_TASK_STATUS_CANCELED);
}
