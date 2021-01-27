/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/private/thread_shared.h>

#include <aws/common/condition_variable.h>
#include <aws/common/linked_list.h>
#include <aws/common/mutex.h>

/*
 * lock guarding the unjoined thread count and pending join list
 */
static struct aws_mutex s_managed_thread_lock = AWS_MUTEX_INIT;
static struct aws_condition_variable s_managed_thread_signal = AWS_CONDITION_VARIABLE_INIT;

/*
 * The number of successfully launched managed threads (or event loop threads which participate by inc/dec) that
 * have not been joined yet.
 */
static uint32_t s_unjoined_thread_count = 0;

/*
 * A list of thread_wrapper structs for threads whose thread function has finished but join has not been called
 * yet for the thread.
 */
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

        /*
         * We lazily join old threads as newer ones finish their thread function.  This means that when called from
         * the main thread, there will always be one last thread (whichever completion serialized last) that is our
         * responsibility to join (as long as at least one managed thread was created).  So we wait for a count <= 1
         * rather than what you'd normally expect (0).
         *
         * We only terminate if there are no threads left so it is possible to spin-wait a while if there is a single
         * thread still running.
         */
        aws_condition_variable_wait_pred(
            &s_managed_thread_signal, &s_managed_thread_lock, s_one_or_fewer_managed_threads_unjoined, NULL);

        done = s_unjoined_thread_count == 0;

        aws_linked_list_init(&join_list);

        aws_linked_list_swap_contents(&join_list, &s_pending_join_managed_threads);

        aws_mutex_unlock(&s_managed_thread_lock);

        /*
         * Join against any finished threads.  These threads are guaranteed to:
         *   (1) Not be the current thread
         *   (2) Have already ran to user thread_function completion
         */
        aws_thread_join_and_free_wrapper_list(&join_list);
    }
}

void aws_thread_pending_join_add(struct aws_linked_list_node *node) {
    struct aws_linked_list join_list;
    aws_linked_list_init(&join_list);

    aws_mutex_lock(&s_managed_thread_lock);
    /*
     * Swap out the pending join threads before adding this, otherwise we'd join against ourselves which won't work
     */
    aws_linked_list_swap_contents(&join_list, &s_pending_join_managed_threads);
    aws_linked_list_push_back(&s_pending_join_managed_threads, node);
    aws_mutex_unlock(&s_managed_thread_lock);

    /*
     * Join against any finished threads.  This thread (it's only ever going to be at most one)
     * is guaranteed to:
     *   (1) Not be the current thread
     *   (2) Has already ran to user thread_function completion
     */
    aws_thread_join_and_free_wrapper_list(&join_list);
}

void aws_thread_initialize_thread_management(void) {
    aws_linked_list_init(&s_pending_join_managed_threads);
}
