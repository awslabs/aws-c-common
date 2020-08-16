/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/ref_count.h>

#include <aws/common/condition_variable.h>
#include <aws/common/mutex.h>

void aws_ref_count_init(struct aws_ref_count *ref_count, void *object, aws_simple_completion_callback *on_zero_fn) {
    aws_atomic_init_int(&ref_count->ref_count, 1);
    ref_count->object = object;
    ref_count->on_zero_fn = on_zero_fn;
}

void *aws_ref_count_acquire(struct aws_ref_count *ref_count) {
    aws_atomic_fetch_add(&ref_count->ref_count, 1);

    return ref_count->object;
}

size_t aws_ref_count_release(struct aws_ref_count *ref_count) {
    size_t old_value = aws_atomic_fetch_sub(&ref_count->ref_count, 1);
    if (old_value == 1) {
        ref_count->on_zero_fn(ref_count->object);
    }

    return old_value - 1;
}

static struct aws_condition_variable s_global_thread_signal;
static struct aws_mutex s_global_thread_lock;
static uint32_t s_global_thread_count;

void aws_global_thread_tracker_init(void) {
    aws_mutex_init(&s_global_thread_lock);
    aws_condition_variable_init(&s_global_thread_signal);
    s_global_thread_count = 0;
}

void aws_global_thread_tracker_clean_up(void) {
    aws_mutex_clean_up(&s_global_thread_lock);
    aws_condition_variable_clean_up(&s_global_thread_signal);
}

void aws_global_thread_tracker_increment(void) {
    aws_mutex_lock(&s_global_thread_lock);
    ++s_global_thread_count;
    aws_mutex_unlock(&s_global_thread_lock);
}

void aws_global_thread_tracker_decrement(void) {
    bool signal = false;
    aws_mutex_lock(&s_global_thread_lock);
    --s_global_thread_count;
    if (s_global_thread_count == 0) {
        signal = true;
    }
    aws_mutex_unlock(&s_global_thread_lock);

    if (signal) {
        aws_condition_variable_notify_one(&s_global_thread_signal);
    }
}

static bool s_thread_count_zero_pred(void *user_data) {
    (void)user_data;

    return s_global_thread_count == 0;
}

void aws_global_thread_shutdown_wait(void) {
    aws_mutex_lock(&s_global_thread_lock);
    aws_condition_variable_wait_pred(&s_global_thread_signal, &s_global_thread_lock, s_thread_count_zero_pred, NULL);
    aws_mutex_unlock(&s_global_thread_lock);
}
