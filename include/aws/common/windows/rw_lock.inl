#ifndef AWS_COMMON_WINDOWS_RW_LOCK_INL
#define AWS_COMMON_WINDOWS_RW_LOCK_INL

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

#ifdef __cplusplus
extern "C" {
#endif

static inline int aws_rw_lock_init(struct aws_rw_lock *lock) {

    InitializeSRWLock(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

static inline void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    (void)lock;
}

static inline int aws_rw_lock_rlock(struct aws_rw_lock *lock) {

    AcquireSRWLockShared(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

static inline int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    AcquireSRWLockExclusive(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

static inline int aws_rw_lock_try_rlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockShared(&lock->lock_handle)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

static inline int aws_rw_lock_try_wlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockExclusive(&lock->lock_handle)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

static inline int aws_rw_lock_runlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockShared(&lock->lock_handle);

    return AWS_OP_SUCCESS;
}

static inline int aws_rw_lock_wunlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockExclusive(&lock->lock_handle);

    return AWS_OP_SUCCESS;
}

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_WINDOWS_RW_LOCK_INL */
