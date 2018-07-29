#ifndef AWS_COMMON_RW_LOCK_H
#define AWS_COMMON_RW_LOCK_H

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
#    include <Windows.h>
#else
#    include <pthread.h>
#endif

struct aws_rw_lock {
#ifdef _WIN32
    SRWLOCK lock_handle;
#else
    pthread_rwlock_t lock_handle;
#endif
};

#ifdef _WIN32
#    define AWS_RW_LOCK_INIT                                                                                           \
        { .lock_handle = SRWLOCK_INIT }
#else
#    define AWS_RW_LOCK_INIT                                                                                           \
        { .lock_handle = PTHREAD_RWLOCK_INITIALIZER }
#endif

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes a new platform instance of mutex.
 */
static inline int aws_rw_lock_init(struct aws_rw_lock *lock);

/**
 * Cleans up internal resources.
 */
static inline void aws_rw_lock_clean_up(struct aws_rw_lock *lock);

/**
 * Blocks until it acquires the lock. While on some platforms such as Windows,
 * this may behave as a reentrant mutex, you should not treat it like one. On
 * platforms it is possible for it to be non-reentrant, it will be.
 */
static inline int aws_rw_lock_rlock(struct aws_rw_lock *lock);
static inline int aws_rw_lock_wlock(struct aws_rw_lock *lock);

/**
 * Attempts to acquire the lock but returns immediately if it can not.
 * While on some platforms such as Windows, this may behave as a reentrant mutex,
 * you should not treat it like one. On platforms it is possible for it to be non-reentrant, it will be.
 */
static inline int aws_rw_lock_try_rlock(struct aws_rw_lock *lock);
static inline int aws_rw_lock_try_wlock(struct aws_rw_lock *lock);

/**
 * Releases the lock.
 */
static inline int aws_rw_lock_runlock(struct aws_rw_lock *lock);
static inline int aws_rw_lock_wunlock(struct aws_rw_lock *lock);

#ifdef __cplusplus
}
#endif

#ifdef _WIN32
#    include <aws/common/windows/rw_lock.inl>
#else
#    include <aws/common/posix/rw_lock.inl>
#endif /* _WIN32 */

#endif /* AWS_COMMON_RW_LOCK_H */
