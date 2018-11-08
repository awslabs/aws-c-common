#ifndef AWS_COMMON_SEMAPHORE_H
#define AWS_COMMON_SEMAPHORE_H
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

#include <aws/common/common.h>
#include <aws/common/condition_variable.h>
#include <aws/common/mutex.h>

struct aws_semaphore {
    size_t count;
    const size_t max_count;
    struct aws_mutex mutex;
    struct aws_condition_variable sync_point;
};

#define AWS_SEMAPHORE_INIT(init, max)                                                                                  \
    { .count = init, .max_count = max, .mutex = AWS_MUTEX_INIT, .sync_point = AWS_CONDITION_VARIABLE_INIT, }

AWS_EXTERN_C_BEGIN

/**
 * Initializes a new instance of semaphore.
 */
AWS_COMMON_API
int aws_semaphore_init(struct aws_semaphore *semaphore, size_t initial_count, size_t max_count);

/**
 * Cleans up internal resources.
 */
AWS_COMMON_API
void aws_semaphore_clean_up(struct aws_semaphore *semaphore);

/**
 * Blocks the current thread until a resource is available.
 */
AWS_COMMON_API
void aws_semaphore_acquire(struct aws_semaphore *semaphore);

/**
 * Release a single resource to the pool.
 */
AWS_COMMON_API
void aws_semaphore_release_one(struct aws_semaphore *semaphore);

/**
 * Release all resources to the pool.
 */
AWS_COMMON_API
void aws_semaphore_release_all(struct aws_semaphore *semaphore);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_SEMAPHORE_H */
