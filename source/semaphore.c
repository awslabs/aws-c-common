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
#include <aws/common/semaphore.h>

#include <assert.h>

int aws_semaphore_init(struct aws_semaphore *semaphore, size_t initial_count, size_t max_count) {

    assert(semaphore);

    AWS_ZERO_STRUCT(*semaphore);

    semaphore->count = initial_count;
    *(size_t *)(&semaphore->max_count) = max_count;
    if (aws_mutex_init(&semaphore->mutex)) {
        return AWS_OP_ERR;
    }
    if (aws_condition_variable_init(&semaphore->sync_point)) {
        aws_mutex_clean_up(&semaphore->mutex);
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_semaphore_clean_up(struct aws_semaphore *semaphore) {

    assert(semaphore);

    aws_mutex_clean_up(&semaphore->mutex);
    aws_condition_variable_clean_up(&semaphore->sync_point);

    AWS_ZERO_STRUCT(*semaphore);
}

bool s_semaphore_wait_pred(void *userdata) {
    struct aws_semaphore *semaphore = userdata;
    return semaphore->count > 0;
}

void aws_semaphore_acquire(struct aws_semaphore *semaphore) {

    assert(semaphore);

    aws_mutex_lock(&semaphore->mutex);

    if (0 == semaphore->count) {
        aws_condition_variable_wait_pred(&semaphore->sync_point, &semaphore->mutex, s_semaphore_wait_pred, semaphore);
    }
    --semaphore->count;

    aws_mutex_unlock(&semaphore->mutex);
}

void aws_semaphore_release_one(struct aws_semaphore *semaphore) {

    assert(semaphore);

    aws_mutex_lock(&semaphore->mutex);

    if (semaphore->count < semaphore->max_count) {
        ++semaphore->count;
    }
    aws_condition_variable_notify_one(&semaphore->sync_point);

    aws_mutex_unlock(&semaphore->mutex);
}

void aws_semaphore_release_all(struct aws_semaphore *semaphore) {

    assert(semaphore);

    aws_mutex_lock(&semaphore->mutex);

    semaphore->count = semaphore->max_count;
    aws_condition_variable_notify_all(&semaphore->sync_point);

    aws_mutex_unlock(&semaphore->mutex);
}
