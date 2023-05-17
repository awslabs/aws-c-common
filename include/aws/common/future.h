#ifndef AWS_COMMON_FUTURE_H
#define AWS_COMMON_FUTURE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_PUSH_SANE_WARNING_LEVEL
AWS_EXTERN_C_BEGIN

struct aws_byte_buf;

struct aws_future;

typedef void(aws_future_on_done_fn)(struct aws_future *future, void *user_data);

typedef void(aws_future_pointer_destructor_fn)(void *value);

enum aws_future_type {
    AWS_FUTURE_POINTER,
    AWS_FUTURE_VALUELESS,
    AWS_FUTURE_BOOL,
    AWS_FUTURE_SIZE,
    AWS_FUTURE_BYTE_BUF,
};

AWS_COMMON_API
struct aws_future *aws_future_new(struct aws_allocator *alloc, enum aws_future_type type);

AWS_COMMON_API
struct aws_future *aws_future_release(struct aws_future *future);

AWS_COMMON_API
struct aws_future *aws_future_acquire(struct aws_future *future);

AWS_COMMON_API
void aws_future_set_error(struct aws_future *future, int error_code);

AWS_COMMON_API
void aws_future_set_pointer(struct aws_future *future, void *value, aws_future_pointer_destructor_fn *destructor);

AWS_COMMON_API
void aws_future_set_valueless(struct aws_future *future);

AWS_COMMON_API
void aws_future_set_bool(struct aws_future *future, bool value);

AWS_COMMON_API
void aws_future_set_size(struct aws_future *future, size_t value);

AWS_COMMON_API
void aws_future_set_byte_buf_passing_ownership(struct aws_future *future, struct aws_byte_buf *value);

AWS_COMMON_API
bool aws_future_is_done(const struct aws_future *future);

AWS_COMMON_API
void aws_future_register_callback(struct aws_future *future, aws_future_on_done_fn *on_done, void *user_data);

AWS_COMMON_API
bool aws_future_register_callback_if_not_done(
    struct aws_future *future,
    aws_future_on_done_fn *on_done,
    void *user_data);

AWS_COMMON_API
bool aws_future_wait(const struct aws_future *future, uint64_t duration_ns);

AWS_COMMON_API
int aws_future_get_error(const struct aws_future *future);

AWS_COMMON_API
void *aws_future_get_pointer(const struct aws_future *future);

AWS_COMMON_API
bool aws_future_get_bool(const struct aws_future *future);

AWS_COMMON_API
size_t aws_future_get_size(const struct aws_future *future);

AWS_COMMON_API
struct aws_byte_buf *aws_future_get_byte_buf(struct aws_future *future);

AWS_COMMON_API
struct aws_byte_buf aws_future_get_byte_buf_taking_ownership(struct aws_future *future);

/* TODO:
    -   support for cancel?
        -   would cancel immediately end the future? or just request that it be canceled? support for both use-cases?
*/

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif /* AWS_COMMON_FUTURE_H */
