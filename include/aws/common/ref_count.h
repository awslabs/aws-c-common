#ifndef AWS_COMMON_REFCOUNT_H
#define AWS_COMMON_REFCOUNT_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

#include <aws/common/atomics.h>

typedef void(aws_on_zero_ref_count_callback)(void *);

/*
 * An type for making ref-counted types, reminiscent of std::shared_ptr in C++
 */
struct aws_ref_count {
    struct aws_atomic_var ref_count;
    void *object;
    aws_on_zero_ref_count_callback *on_zero_fn;
};

AWS_EXTERN_C_BEGIN

/**
 * Initializes a ref-count tracking structure.
 *
 * @param ref_count ref-counter to initialize
 * @param object object being ref counted
 * @param on_zero_fn function to invoke when the ref count reaches zero
 */
AWS_COMMON_API void aws_ref_count_init(
    struct aws_ref_count *ref_count,
    void *object,
    aws_on_zero_ref_count_callback *on_zero_fn);

/**
 * Increments a ref count tracker's ref count
 *
 * @param ref_count ref-counter to increment the count for
 * @return the object being ref-counted
 */
AWS_COMMON_API void *aws_ref_count_acquire(struct aws_ref_count *ref_count);

/**
 * Decrements a ref count tracker's ref count.  Invokes the on_zero callback if the ref count drops to zero
 * @param ref_count ref-counter to decrement the count for
 * @return the value of the decremented ref count
 */
AWS_COMMON_API size_t aws_ref_count_release(struct aws_ref_count *ref_count);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_REFCOUNT_H */
