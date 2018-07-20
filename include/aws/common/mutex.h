#ifndef AWS_COMMON_MUTEX_H_
#define AWS_COMMON_MUTEX_H_

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
#ifndef _WIN32
#include <pthread.h>
#endif

struct aws_mutex {
#ifdef _WIN32
    SRWLOCK mutex_handle;
#else
    pthread_mutex_t mutex_handle;
#endif
};

#ifdef _WIN32
#define AWS_MUTEX_INIT                                                                                                 \
{ .mutex_handle = SRWLOCK_INIT }
#else
#define AWS_MUTEX_INIT                                                                                                 \
{ .mutex_handle = PTHREAD_MUTEX_INITIALIZER }
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes a new platform instance of mutex.
 */
AWS_COMMON_API int aws_mutex_init(struct aws_mutex *mutex);

/**
 * Cleans up internal resources.
 */
AWS_COMMON_API void aws_mutex_clean_up(struct aws_mutex *mutex);

/**
 * Blocks until it acquires the lock. While on some platforms such as Windows, this may behave as a reentrant mutex,
 * you should not treat it like one. On platforms it is possible for it to be non-reentrant, it will be.
 */
AWS_COMMON_API int aws_mutex_lock(struct aws_mutex *mutex);

/**
 * Attempts to acquire the lock but returns immediately if it can not.
 * While on some platforms such as Windows, this may behave as a reentrant mutex,
 * you should not treat it like one. On platforms it is possible for it to be non-reentrant, it will be.
*/
AWS_COMMON_API int aws_mutex_try_lock(struct aws_mutex *mutex);

/**
 * Releases the lock.
 */
AWS_COMMON_API int aws_mutex_unlock(struct aws_mutex *mutex);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_MUTEX_H_ */
