/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/future.h>

#include <aws/common/byte_buf.h>
#include <aws/common/condition_variable.h>
#include <aws/common/mutex.h>
#include <aws/common/ref_count.h>

/* TODO:
 - logging
 */

union aws_future_value_union {
    int error_code;
    struct {
        void *value;
        aws_future_pointer_destructor_fn *destructor;
    } pointer;
    bool boolean;
    size_t size;
    struct aws_byte_buf byte_buf;
};

struct aws_future {
    struct aws_allocator *alloc;
    struct aws_ref_count ref_count;
    struct aws_mutex lock;
    struct aws_condition_variable wait_cvar;
    aws_future_on_done_fn *on_done_cb;
    void *on_done_user_data;

    enum aws_future_type type;
    union aws_future_value_union val_u;

    bool is_done;
    bool is_error;
};

static void s_future_value_union_clean_up(union aws_future_value_union *val_u, enum aws_future_type type) {
    switch (type) {
        case AWS_FUTURE_POINTER:
            if (val_u->pointer.destructor) {
                val_u->pointer.destructor(val_u->pointer.value);
            }
            break;

        case AWS_FUTURE_BYTE_BUF:
            aws_byte_buf_clean_up(&val_u->byte_buf);
            break;

        default:
            break;
    }
}

static void s_future_destroy(void *user_data) {
    struct aws_future *future = user_data;

    s_future_value_union_clean_up(&future->val_u, future->type);
    aws_condition_variable_clean_up(&future->wait_cvar);
    aws_mutex_clean_up(&future->lock);
    aws_mem_release(future->alloc, future);
}

struct aws_future *aws_future_new(struct aws_allocator *alloc, enum aws_future_type type) {
    AWS_ASSERT(alloc != NULL);

    struct aws_future *future = aws_mem_calloc(alloc, 1, sizeof(struct aws_future));
    future->alloc = alloc;
    future->type = type;
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
    if (future != NULL) {
        aws_ref_count_acquire(&future->ref_count);
    }
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

bool aws_future_wait(const struct aws_future *future, uint64_t duration_ns) {
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

void aws_future_register_callback(struct aws_future *future, aws_future_on_done_fn *on_done, void *user_data) {

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
        on_done(future, user_data);
    }
}

bool aws_future_is_done_else_register_callback(
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

static void s_future_set_done(struct aws_future *future, union aws_future_value_union *val_u, bool is_error) {

    /* BEGIN CRITICAL SECTION */
    aws_mutex_lock(&future->lock);

    aws_future_on_done_fn *on_done_cb = future->on_done_cb;
    void *on_done_user_data = future->on_done_user_data;

    bool first_time = !future->is_done;
    if (first_time) {
        future->is_done = true;
        future->is_error = is_error;
        future->val_u = *val_u;
        future->on_done_cb = NULL;
        future->on_done_user_data = NULL;

        aws_condition_variable_notify_all(&future->wait_cvar);
    }

    aws_mutex_unlock(&future->lock);
    /* END CRITICAL SECTION */

    if (first_time) {
        /* invoke done callback outside critical section to avoid deadlock */
        if (on_done_cb) {
            on_done_cb(future, on_done_user_data);
        }
    } else if (!is_error) {
        /* future was already done, so just destroy this newer value */
        s_future_value_union_clean_up(val_u, future->type);
    }
}

void aws_future_set_error(struct aws_future *future, int error_code) {
    AWS_ASSERT(future != NULL);

    /* handle recoverable usage error */
    AWS_ASSERT(error_code != 0);
    if (AWS_UNLIKELY(error_code == 0)) {
        error_code = AWS_ERROR_UNKNOWN;
    }

    union aws_future_value_union val_u = {.error_code = error_code};
    s_future_set_done(future, &val_u, true /*is_error*/);
}

void aws_future_set_pointer(struct aws_future *future, void *value, aws_future_pointer_destructor_fn *destructor) {
    AWS_ASSERT(future != NULL);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_POINTER && "This future's result value must be a pointer");
    AWS_FATAL_ASSERT(value != NULL && "This future's result value cannot be NULL");
    AWS_FATAL_ASSERT(destructor != NULL && "This future's result value must have a destructor");

    union aws_future_value_union val_u = {
        .pointer = {.value = value, .destructor = destructor},
    };
    s_future_set_done(future, &val_u, false /*is_error*/);
}

void aws_future_set_valueless(struct aws_future *future) {
    AWS_ASSERT(future != NULL);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_VALUELESS && "This future's result must be valueless");

    union aws_future_value_union val_u;
    AWS_ZERO_STRUCT(val_u);
    s_future_set_done(future, &val_u, false /*is_error*/);
}

void aws_future_set_bool(struct aws_future *future, bool value) {
    AWS_ASSERT(future != NULL);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_BOOL && "This future's result value must be a bool");

    union aws_future_value_union val_u = {.boolean = value};
    s_future_set_done(future, &val_u, false /*is_error*/);
}

void aws_future_set_size(struct aws_future *future, size_t value) {
    AWS_ASSERT(future != NULL);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_SIZE && "This future's result value must be a size_t");

    union aws_future_value_union val_u = {.size = value};
    s_future_set_done(future, &val_u, false /*is_error*/);
}

void aws_future_set_byte_buf_passing_ownership(struct aws_future *future, struct aws_byte_buf *value) {
    AWS_ASSERT(future != NULL);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_BYTE_BUF && "This future's result value must be an aws_byte_buf");

    /* transfer ownership by doing a by-value copy, and zeroing out the old location */
    union aws_future_value_union val_u = {.byte_buf = *value};
    AWS_ZERO_STRUCT(*value);

    s_future_set_done(future, &val_u, false /*is_error*/);
}

int aws_future_get_error(const struct aws_future *future) {
    AWS_ASSERT(future != NULL);
    /* not bothering with lock because all the "get" functions must only be called after the future is done */
    AWS_FATAL_ASSERT(future->is_done && "Cannot get error before future is done");
    return future->is_error ? future->val_u.error_code : 0;
}

#define AWS_FUTURE_GET_VALUE_PRECONDITIONS(future)                                                                     \
    do {                                                                                                               \
        AWS_ASSERT(future != NULL);                                                                                    \
        AWS_FATAL_ASSERT(future->is_done && "Cannot get value before future is done");                                 \
        AWS_FATAL_ASSERT(!future->is_error && "Cannot get value from future that failed with an error");               \
    } while (0)

void *aws_future_get_pointer(const struct aws_future *future) {
    AWS_FUTURE_GET_VALUE_PRECONDITIONS(future);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_POINTER && "Cannot get pointer from this type of future");
    return future->val_u.pointer.value;
}

bool aws_future_get_bool(const struct aws_future *future) {
    AWS_FUTURE_GET_VALUE_PRECONDITIONS(future);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_BOOL && "Cannot get bool from this type of future");
    return future->val_u.boolean;
}

size_t aws_future_get_size(const struct aws_future *future) {
    AWS_FUTURE_GET_VALUE_PRECONDITIONS(future);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_SIZE && "Cannot get size_t from this type of future");
    return future->val_u.size;
}

struct aws_byte_buf *aws_future_get_byte_buf(struct aws_future *future) {
    AWS_FUTURE_GET_VALUE_PRECONDITIONS(future);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_BYTE_BUF && "Cannot get aws_byte_buf from this type of future");
    return &future->val_u.byte_buf;
}

struct aws_byte_buf aws_future_get_byte_buf_taking_ownership(struct aws_future *future) {
    AWS_FUTURE_GET_VALUE_PRECONDITIONS(future);
    AWS_FATAL_ASSERT(future->type == AWS_FUTURE_BYTE_BUF && "Cannot get aws_byte_buf from this type of future");

    /* transfer ownership by returning a by-value copy, while zeroing out the old location */
    struct aws_byte_buf tmp = future->val_u.byte_buf;
    AWS_ZERO_STRUCT(future->val_u.byte_buf);
    return tmp;
}
