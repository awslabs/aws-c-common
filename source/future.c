/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/future.h>

#include <aws/common/mutex.h>
#include <aws/common/ref_count.h>

/* TODO:
 - logging
 */

struct aws_future {
    struct aws_allocator *alloc;
    struct aws_ref_count ref_count;
    struct aws_mutex lock;
    aws_future_on_complete_fn *on_complete_cb;
    void *on_complete_user_data;
    void *value;
    void (*value_dtor)(void *);
    int error_code;
    bool is_complete;
};

static void s_future_destroy(void *user_data) {
    struct aws_future *future = user_data;

    /* If no one took ownership of the value, call its destructor */
    if (future->value_dtor) {
        future->value_dtor(value);
    }

    aws_mutex_clean_up(&future->lock);
}

struct aws_future *aws_future_new(struct aws_allocator *alloc) {
    AWS_ASSERT(alloc != NULL);

    struct aws_future *future = aws_mem_calloc(alloc, 1, sizeof(struct aws_future));
    future->alloc = alloc;
    aws_ref_count_init(&future->ref_count, future, s_future_destroy);
    aws_mutex_init(&future->lock);
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

bool aws_future_is_complete(const struct aws_future *future) {
    AWS_ASSERT(future);

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&((struct aws_future *)future)->lock);
    bool is_complete = future->is_complete;
    aws_mutex_unlock(&((struct aws_future *)future)->lock);
    /* END CRITICAL SECTION */

    return is_complete;
}

void aws_future_set_completion_callback(
    struct aws_future *future,
    aws_future_on_complete_fn *on_complete,
    void *user_data) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    AWS_FATAL_ASSERT(future->on_complete_cb == NULL && "Future completion callback must only be set once");

    bool is_complete = future->is_complete;

    /* if incomplete, store callback for later */
    if (!is_complete) {
        future->on_complete_cb = on_complete;
        future->on_complete_user_data = user_data;
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    /* if already complete, fire callback now */
    if (is_complete) {
        on_complete(user_data);
    }
}

bool aws_future_is_complete_else_set_callback(
    struct aws_future *future,
    aws_future_on_complete_fn *on_complete,
    void *on_complete_user_data) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    AWS_FATAL_ASSERT(future->on_complete_cb == NULL && "Future completion callback must only be set once");

    bool is_complete = future->is_complete;
    if (!is_complete) {
        future->on_complete_cb = on_complete;
        future->on_complete_user_data = on_complete_user_data;
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    return is_complete;
}

static void s_future_set_complete(
    struct aws_future *future,
    void *value,
    aws_future_value_dtor_fn *value_dtor,
    error_code) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    AWS_FATAL_ASSERT(!future->is_complete && "The future must complete exactly once");

    future->is_complete = true;
    future->value = value;
    future->value_dtor = value_dtor;
    future->error_code = error_code;

    aws_future_on_complete_fn *on_complete_cb = future->on_complete_cb;
    void *on_complete_user_data = future->on_complete_user_data;

    future->on_complete_cb = NULL;
    future->on_complete_user_data = NULL;

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    /* Invoke completion callback outside critical section to avoid deadlock */
    if (on_complete_cb) {
        on_complete_cb(on_complete_user_data);
    }

    return AWS_OP_SUCCESS;
}

void aws_future_set_value(struct aws_future *future, void *value, aws_future_value_dtor_fn *dtor) {
    AWS_ASSERT(future != NULL);

    AWS_FATAL_ASSERT(value != NULL && "The future's result value cannot be NULL");
    AWS_FATAL_ASSERT(dtor != NULL && "The future's result value must have a destructor");

    return s_future_set_complete(future, value, dtor, 0 /*error_code*/);
}

int aws_future_set_error(struct aws_future *future, int error_code) {
    AWS_ASSERT(future != NULL);

    /* handle recoverable usage error */
    AWS_ASSERT(error_code != 0);
    if (AWS_UNLIKELY(error_code == 0)) {
        error_code = AWS_ERROR_UNKNOWN;
    }

    return s_future_set_complete(future, NULL /*value*/, NULL /*value_dtor*/, error_code);
}

void *aws_future_take_value(struct aws_future *future) {
    AWS_ASSERT(future != NULL);

    /* not bothering with lock because this function must only be called after the future is complete,
     * and must only be called once */
    AWS_FATAL_ASSERT(future->is_complete && "Cannot take value from incomplete future");
    AWS_FATAL_ASSERT(future->value_dtor && "Cannot take value from future multiple times");

    /* relinquish ownership of the value */
    future->value_dtor = NULL;

    if (future->error_code != 0) {
        aws_raise_error(future->error_code);
        return NULL;
    } else {
        return future->value;
    }
}
