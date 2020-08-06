#ifndef AWS_COMMON_REFCOUNT_H
#define AWS_COMMON_REFCOUNT_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

/*
 * Common macro that implements a null-safe release function for all ref-counted types.
 */
#define AWS_REF_COUNT_RELEASE_IMPL(object, refcount_member_name, destroy_fn)                                           \
    {                                                                                                                  \
        if (object == NULL) {                                                                                          \
            return;                                                                                                    \
        }                                                                                                              \
                                                                                                                       \
        size_t old_value = aws_atomic_fetch_sub(&object->refcount_member_name, 1);                                     \
        if (old_value == 1) {                                                                                          \
            destroy_fn(object);                                                                                        \
        }                                                                                                              \
    }

/*
 * Common macro that implements a null-safe acquire function for all ref-counted types.
 * Assumes the function signature for acquire() returns the object
 * itself, which lets us simplify the common initialization pattern from:
 *
 * something.object = object;
 * aws_object_acquire(object);
 *
 * to
 *
 * something.object = aws_object_acquire(object);
 */
#define AWS_REF_COUNT_ACQUIRE_IMPL(object, refcount_member_name)                                                       \
    {                                                                                                                  \
        if (object != NULL) {                                                                                          \
            aws_atomic_fetch_add(&object->refcount_member_name, 1);                                                    \
        }                                                                                                              \
                                                                                                                       \
        return object;                                                                                                 \
    }

#endif /* AWS_COMMON_REFCOUNT_H */
