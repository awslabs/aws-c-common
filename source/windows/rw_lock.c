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

#include <aws/common/rw_lock.h>

int aws_rw_lock_init(struct aws_rw_lock *lock) {

    InitializeSRWLock(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    (void)lock;
}

int aws_rw_lock_rdlock(struct aws_rw_lock *lock) {

    AcquireSRWLockShared(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wrlock(struct aws_rw_lock *lock) {

    AcquireSRWLockExclusive(&lock->lock_handle);
    return AWS_OP_SUCCESS;
}

int aws_rw_lock_try_rdlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockShared(&lock->lock_handle)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_rw_lock_try_wrlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockExclusive(&lock->lock_handle)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_rw_lock_rdunlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockShared(&lock->lock_handle);

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wrunlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockExclusive(&lock->lock_handle);

    return AWS_OP_SUCCESS;
}
