/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/ref_count.h>

void aws_ref_count_init(struct aws_ref_count *ref_count, void *object, aws_on_zero_ref_count_callback *on_zero_fn) {
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
