/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/future.h>

#include <aws/common/condition_variable.h>
#include <aws/common/mutex.h>
#include <aws/common/ref_count.h>

/* TODO:
 - logging
 */

struct aws_future {
    struct aws_allocator *alloc;
    struct aws_ref_count ref_count;
    struct aws_mutex lock;
    struct aws_condition_variable wait_cvar;
    aws_future_on_done_fn *on_done_cb;
    void *on_done_user_data;
    void *value;
    void (*value_destructor)(void *);
    int error_code;
    bool is_done;
};

static void s_future_destroy(void *user_data) {
    struct aws_future *future = user_data;

    /* If no one took ownership of the value, call its destructor */
    if (future->value_destructor) {
        future->value_destructor(future->value);
    }

    aws_condition_variable_clean_up(&future->wait_cvar);
    aws_mutex_clean_up(&future->lock);
}

struct aws_future *aws_future_new(struct aws_allocator *alloc) {
    AWS_ASSERT(alloc != NULL);

    struct aws_future *future = aws_mem_calloc(alloc, 1, sizeof(struct aws_future));
    future->alloc = alloc;
    aws_ref_count_init(&future->ref_count, future, s_future_destroy);
    aws_mutex_init(&future->lock);
    aws_condition_variable_init(&future->wait_cvar);
    return future;
}

struct aws_future *aws_future_release(struct aws_future *future) {
    if (future != NULL) {
        aws_ref_count_release(&future->ref_count);
    }
    return NULL;
}

struct aws_future *aws_future_acquire(struct aws_future *future) {
    AWS_ASSERT(future != NULL);
    aws_ref_count_acquire(&future->ref_count);
    return future;
}

bool aws_future_is_done(const struct aws_future *future) {
    AWS_ASSERT(future);

    /* this function is conceptually const, but we need to hold the lock a moment */
    struct aws_mutex *mutable_lock = (struct aws_mutex *)&future->lock;

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(mutable_lock);
    bool is_done = future->is_done;
    aws_mutex_unlock(mutable_lock);
    /* END CRITICAL SECTION */

    return is_done;
}

static bool s_future_is_done_pred(void *user_data) {
    struct aws_future *future = user_data;
    return future->is_done;
}

bool aws_future_is_done_after_wait(const struct aws_future *future, uint64_t duration_ns) {
    AWS_ASSERT(future);

    /* this function is conceptually const, but we need to use synchronization primitives */
    struct aws_future *mutable_future = (struct aws_future *)future;

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&mutable_future->lock);

    bool is_done = aws_condition_variable_wait_for_pred(
                       &mutable_future->wait_cvar,
                       &mutable_future->lock,
                       (int64_t)duration_ns,
                       s_future_is_done_pred,
                       mutable_future) == AWS_OP_SUCCESS;

    aws_mutex_unlock(&mutable_future->lock);
    /* END CRITICAL SECTION */

    return is_done;
}

void aws_future_set_done_callback(struct aws_future *future, aws_future_on_done_fn *on_done, void *user_data) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    AWS_FATAL_ASSERT(future->on_done_cb == NULL && "Future done callback must only be set once");

    bool is_done = future->is_done;

    /* if not done, store callback for later */
    if (!is_done) {
        future->on_done_cb = on_done;
        future->on_done_user_data = user_data;
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    /* if already done, fire callback now */
    if (is_done) {
        on_done(user_data);
    }
}

bool aws_future_is_done_else_set_callback(
    struct aws_future *future,
    aws_future_on_done_fn *on_done,
    void *on_done_user_data) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    AWS_FATAL_ASSERT(future->on_done_cb == NULL && "Future done callback must only be set once");

    bool is_done = future->is_done;
    if (!is_done) {
        future->on_done_cb = on_done;
        future->on_done_user_data = on_done_user_data;
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    return is_done;
}

static void s_future_set_done(
    struct aws_future *future,
    void *value,
    aws_future_value_destructor_fn *value_destructor,
    int error_code) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    aws_future_on_done_fn *on_done_cb = future->on_done_cb;
    void *on_done_user_data = future->on_done_user_data;

    bool first_time = !future->is_done;
    if (first_time) {
        future->is_done = true;
        future->value = value;
        future->value_destructor = value_destructor;
        future->error_code = error_code;
        future->on_done_cb = NULL;
        future->on_done_user_data = NULL;

        aws_condition_variable_notify_all(&future->wait_cvar);
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    if (first_time) {
        /* invoke done callback outside critical section to avoid deadlock */
        if (on_done_cb) {
            on_done_cb(on_done_user_data);
        }

    } else if (value_destructor != NULL) {
        /* future was already done, so just destroy this newer value */
        value_destructor(value);
    }
}

void aws_future_set_value(struct aws_future *future, void *value, aws_future_value_destructor_fn *destructor) {
    AWS_ASSERT(future != NULL);

    AWS_FATAL_ASSERT(value != NULL && "The future's result value cannot be NULL");
    AWS_FATAL_ASSERT(destructor != NULL && "The future's result value must have a destructor");

    s_future_set_done(future, value, destructor, 0 /*error_code*/);
}

void aws_future_set_error(struct aws_future *future, int error_code) {
    AWS_ASSERT(future != NULL);

    /* handle recoverable usage error */
    AWS_ASSERT(error_code != 0);
    if (AWS_UNLIKELY(error_code == 0)) {
        error_code = AWS_ERROR_UNKNOWN;
    }

    s_future_set_done(future, NULL /*value*/, NULL /*value_destructor*/, error_code);
}

void *aws_future_take_value(struct aws_future *future) {
    AWS_ASSERT(future != NULL);

    /* not bothering with lock because this function must only be called after the future is done,
     * and must only be called once */
    AWS_FATAL_ASSERT(future->is_done && "Cannot take value before future is done");
    AWS_FATAL_ASSERT(future->value_destructor != NULL && "Cannot take value from future multiple times");

    if (future->error_code != 0) {
        aws_raise_error(future->error_code);
        return NULL;
    } else {
        /* relinquish ownership of the value */
        void *value = future->value;
        future->value = NULL;
        future->value_destructor = NULL;
        return value;
    }
}
