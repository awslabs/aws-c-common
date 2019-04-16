/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/weak_ref.h>

#include <aws/common/atomics.h>
#include <aws/common/mutex.h>

#include <assert.h>

struct aws_weak_ref {
    struct aws_allocator *allocator;
    void *object;
    struct aws_mutex lock;
    struct aws_atomic_var ref_count;
};

static void s_aws_weak_ref_destroy(struct aws_weak_ref *ref) {
    if (ref == NULL) {
        return;
    }

    assert(aws_atomic_load_int(&ref->ref_count) == 0);

    aws_mutex_clean_up(&ref->lock);
    aws_mem_release(ref->allocator, ref);
}

struct aws_weak_ref *aws_weak_ref_new(struct aws_allocator *allocator, void *object) {
    assert(object != NULL);
    if (object == NULL) {
        return NULL;
    }

    struct aws_weak_ref *weak_ref = aws_mem_acquire(allocator, sizeof(struct aws_weak_ref));
    if (weak_ref == NULL) {
        return NULL;
    }

    AWS_ZERO_STRUCT(*weak_ref);
    weak_ref->allocator = allocator;
    weak_ref->object = object;
    if (aws_mutex_init(&weak_ref->lock)) {
        goto on_error;
    }

    aws_atomic_init_int(&weak_ref->ref_count, 1);

    return weak_ref;

on_error:

    s_aws_weak_ref_destroy(weak_ref);

    return NULL;
}

void aws_weak_ref_acquire(struct aws_weak_ref *ref) {
    aws_atomic_fetch_add(&ref->ref_count, 1);
}

void aws_weak_ref_release(struct aws_weak_ref *ref) {
    size_t old_value = aws_atomic_fetch_sub(&ref->ref_count, 1);
    if (old_value == 1) {
        s_aws_weak_ref_destroy(ref);
    }
}

void *aws_weak_ref_lock(struct aws_weak_ref *ref) {
    aws_mutex_lock(&ref->lock);
    return ref->object;
}

void aws_weak_ref_unlock(struct aws_weak_ref *ref) {
    aws_mutex_unlock(&ref->lock);
}

void aws_weak_ref_set(struct aws_weak_ref *ref, void *object) {
    aws_mutex_lock(&ref->lock);
    ref->object = object;
    aws_mutex_unlock(&ref->lock);
}
