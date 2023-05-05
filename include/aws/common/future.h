#ifndef AWS_COMMON_FUTURE_H
#define AWS_COMMON_FUTURE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

struct aws_future;

typedef void(aws_future_on_done_fn)(void *user_data);

typedef void(aws_future_value_destructor_fn)(void *value);

AWS_COMMON_API
struct aws_future *aws_future_new(struct aws_allocator *alloc);

AWS_COMMON_API
struct aws_future *aws_future_release(struct aws_future *future);

AWS_COMMON_API
struct aws_future *aws_future_acquire(struct aws_future *future);

AWS_COMMON_API
void aws_future_set_value(struct aws_future *future, void *value, aws_future_value_destructor_fn *destructor);

AWS_COMMON_API
void aws_future_set_error(struct aws_future *future, int error_code);

AWS_COMMON_API
void aws_future_set_void(struct aws_future *future);

AWS_COMMON_API
bool aws_future_is_done(const struct aws_future *future);

AWS_COMMON_API
void aws_future_set_done_callback(
    struct aws_future *future,
    aws_future_value_destructor_fn *on_complete,
    void *user_data);

AWS_COMMON_API
bool aws_future_is_done_else_set_callback(
    struct aws_future *future,
    aws_future_value_destructor_fn *on_complete,
    void *on_complete_user_data);

AWS_COMMON_API
bool aws_future_is_done_after_wait(const struct aws_future *future, uint64_t duration_ns);

AWS_COMMON_API
void *aws_future_take_value(struct aws_future *future);

AWS_COMMON_API
void *aws_future_get_error(struct aws_future *future);

/* TODO:
    -   support for cancel?
        -   would cancel immediately end the future? or just request that it be canceled? support for both use-cases?
*/

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FUTURE_H */
