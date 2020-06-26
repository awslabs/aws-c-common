/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/rw_lock.h>

#include <Windows.h>
#include <synchapi.h>

/* Ensure our rwlock and Windows' rwlocks are the same size */
AWS_STATIC_ASSERT(sizeof(SRWLOCK) == sizeof(struct aws_rw_lock));

int aws_rw_lock_init(struct aws_rw_lock *lock) {

    InitializeSRWLock(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    (void)lock;
}

int aws_rw_lock_rlock(struct aws_rw_lock *lock) {

    AcquireSRWLockShared(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    AcquireSRWLockExclusive(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

int aws_rw_lock_try_rlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockShared(AWSSRW_TO_WINDOWS(lock))) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_rw_lock_try_wlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockExclusive(AWSSRW_TO_WINDOWS(lock))) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_rw_lock_runlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockShared(AWSSRW_TO_WINDOWS(lock));

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wunlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockExclusive(AWSSRW_TO_WINDOWS(lock));

    return AWS_OP_SUCCESS;
}
