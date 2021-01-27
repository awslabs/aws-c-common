/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/thread_shared.h>

#include <aws/common/condition_variable.h>
#include <aws/common/linked_list.h>
#include <aws/common/mutex.h>

static struct aws_mutex s_managed_thread_lock = AWS_MUTEX_INIT;
static struct aws_condition_variable s_managed_thread_signal = AWS_CONDITION_VARIABLE_INIT;
static uint32_t s_unjoined_thread_count = 0;
static struct aws_linked_list s_pending_join_managed_threads;

void aws_thread_increment_unjoined_count(void) {
    aws_mutex_lock(&s_managed_thread_lock);
    ++s_unjoined_thread_count;
    aws_mutex_unlock(&s_managed_thread_lock);
}

void aws_thread_decrement_unjoined_count(void) {
    aws_mutex_lock(&s_managed_thread_lock);
    --s_unjoined_thread_count;
    aws_mutex_unlock(&s_managed_thread_lock);
    aws_condition_variable_notify_one(&s_managed_thread_signal);
}

bool s_one_or_fewer_managed_threads_unjoined(void *context) {
    (void)context;
    return s_unjoined_thread_count <= 1;
}

void aws_thread_join_all_managed(void) {
    struct aws_linked_list join_list;

    bool done = false;
    while (!done) {
        aws_mutex_lock(&s_managed_thread_lock);
        aws_condition_variable_wait_pred(
            &s_managed_thread_signal, &s_managed_thread_lock, s_one_or_fewer_managed_threads_unjoined, NULL);

        done = s_unjoined_thread_count == 0;

        aws_linked_list_init(&join_list);

        aws_linked_list_swap_contents(&join_list, &s_pending_join_managed_threads);

        aws_mutex_unlock(&s_managed_thread_lock);

        aws_thread_join_and_free_wrapper_list(&join_list);
    }
}

void aws_thread_pending_join_add(struct aws_linked_list_node *node) {
    struct aws_linked_list join_list;
    aws_linked_list_init(&join_list);

    aws_mutex_lock(&s_managed_thread_lock);
    aws_linked_list_swap_contents(&join_list, &s_pending_join_managed_threads);
    aws_linked_list_push_back(&s_pending_join_managed_threads, node);
    aws_mutex_unlock(&s_managed_thread_lock);

    aws_thread_join_and_free_wrapper_list(&join_list);
}

void aws_thread_initialize_thread_management(void) {
    aws_linked_list_init(&s_pending_join_managed_threads);
}
