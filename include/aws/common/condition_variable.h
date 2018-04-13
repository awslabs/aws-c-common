#ifndef AWS_CONDITION_VARIABLE_H
#define AWS_CONDITION_VARIABLE_H

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
#ifdef _WIN32
#include <Windows.h>
#else
#include <pthread.h>
#endif

struct aws_mutex;

struct aws_condition_variable {
#ifdef _WIN32
    CONDITION_VARIABLE condition_handle;
#else
    pthread_cond_t condition_handle;
#endif
};

/**
 * Static initializer for condition variable.
 * You can do something like struct aws_condition_variable var = AWS_CONDITION_VARIABLE_INIT;
 */
#ifdef _WIN32
#define AWS_CONDITION_VARIABLE_INIT                                                                                    \
{ .condition_handle = CONDITION_VARIABLE_INIT }
#else
#define AWS_CONDITION_VARIABLE_INIT                                                                                    \
{ .condition_handle = PTHREAD_COND_INITIALIZER }
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes a condition variable.
 */
AWS_COMMON_API int aws_condition_variable_init (struct aws_condition_variable *condition_variable);

/**
 * Cleans up a condition variable.
 */
AWS_COMMON_API void aws_condition_variable_clean_up (struct aws_condition_variable *condition_variable);

/**
 * Notifies/Wakes one waiting thread
 */
AWS_COMMON_API int aws_condition_variable_notify_one (struct aws_condition_variable *condition_variable);

/**
 * Notifies/Wakes all waiting threads.
 */
AWS_COMMON_API int aws_condition_variable_notify_all (struct aws_condition_variable *condition_variable);

/**
 * Waits the calling thread on a notification from another thread.
 */
AWS_COMMON_API int aws_condition_variable_wait (struct aws_condition_variable *condition_variable, struct aws_mutex *mutex);

/**
 * Waits the calling thread on a notification from another thread. Times out after time_to_wait. time_to_wait is in nanoseconds.
 */
AWS_COMMON_API int aws_condition_variable_wait_until (struct aws_condition_variable *condition_variable, struct aws_mutex *mutex,
                                                    uint64_t time_to_wait);

#ifdef __cplusplus
}
#endif

#endif /*AWS_CONDITION_VARIABLE_H */
