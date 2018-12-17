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
/* NOTE: Do not use this macro before including Windows.h */
#    define AWSSRW_TO_WINDOWS(pCV) (PSRWLOCK) pCV
#else
#    include <aws/common/atomics.h>
#    include <aws/common/mutex.h>
#    include <aws/common/semaphore.h>
#endif

struct aws_rw_lock {
#ifdef _WIN32
    void *lock_handle;
#else
    struct aws_atomic_var readers;
    struct aws_atomic_var holdouts;
    struct aws_semaphore reader_sem;
    struct aws_semaphore writer_sem;
    struct aws_mutex writer_lock;
#endif
};

#ifdef _WIN32
#    define AWS_RW_LOCK_INIT                                                                                           \
        { .lock_handle = NULL }
#elif SIZE_MAX == UINT32_MAX
#    define AWS_RW_LOCK_INIT                                                                                           \
        {                                                                                                              \
            .readers = AWS_ATOMIC_INIT_INT(0), .holdouts = AWS_ATOMIC_INIT_INT(0),                                     \
            .reader_sem = AWS_SEMAPHORE_INIT(0, INT32_MAX), .writer_sem = AWS_SEMAPHORE_INIT(0, 1),                    \
            .writer_lock = AWS_MUTEX_INIT,                                                                             \
        }
#else
#    define AWS_RW_LOCK_INIT                                                                                           \
        {                                                                                                              \
            .readers = AWS_ATOMIC_INIT_INT(0), .holdouts = AWS_ATOMIC_INIT_INT(0),                                     \
            .reader_sem = AWS_SEMAPHORE_INIT(0, INT64_MAX), .writer_sem = AWS_SEMAPHORE_INIT(0, 1),                    \
            .writer_lock = AWS_MUTEX_INIT,                                                                             \
        }
#endif

AWS_EXTERN_C_BEGIN

/**
 * Initializes a new platform instance of rw_lock.
 */
AWS_COMMON_API int aws_rw_lock_init(struct aws_rw_lock *lock);

/**
 * Cleans up internal resources.
 */
AWS_COMMON_API void aws_rw_lock_clean_up(struct aws_rw_lock *lock);

/**
 * Enters the lock in reader-mode. This call blocks if there are any open writers.
 */
AWS_COMMON_API int aws_rw_lock_rlock(struct aws_rw_lock *lock);

/**
 * Enters the lock in writer-mode. This call blocks if there are any open readers.
 * Note: You may not use this call to upgrade from reader to writer mode, the lock must be unlocked.
 */
AWS_COMMON_API int aws_rw_lock_wlock(struct aws_rw_lock *lock);

/**
 * Releases the lock from reader mode.
 * If any writers are waiting and this is the last reader, the writer will enter the lock.
 */
AWS_COMMON_API int aws_rw_lock_runlock(struct aws_rw_lock *lock);

/**
 * Release the lock from writer mode.
 * If any readers are waiting, they will all enter the lock.
 */
AWS_COMMON_API int aws_rw_lock_wunlock(struct aws_rw_lock *lock);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_RW_LOCK_H */
