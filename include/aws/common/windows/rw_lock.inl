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

AWS_EXTERN_C_BEGIN

#include <Windows.h>

/* Ensure our rwlock and Windows' rwlocks are the same size */
AWS_STATIC_ASSERT(sizeof(SRWLOCK) == sizeof(struct aws_rw_lock));

AWS_STATIC_IMPL int aws_rw_lock_init(struct aws_rw_lock *lock) {

    InitializeSRWLock(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    (void)lock;
}

AWS_STATIC_IMPL int aws_rw_lock_rlock(struct aws_rw_lock *lock) {

    AcquireSRWLockShared(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    AcquireSRWLockExclusive(AWSSRW_TO_WINDOWS(lock));
    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL int aws_rw_lock_try_rlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockShared(AWSSRW_TO_WINDOWS(lock))) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

AWS_STATIC_IMPL int aws_rw_lock_try_wlock(struct aws_rw_lock *lock) {

    if (TryAcquireSRWLockExclusive(AWSSRW_TO_WINDOWS(lock))) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

AWS_STATIC_IMPL int aws_rw_lock_runlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockShared(AWSSRW_TO_WINDOWS(lock));

    return AWS_OP_SUCCESS;
}

AWS_STATIC_IMPL int aws_rw_lock_wunlock(struct aws_rw_lock *lock) {

    ReleaseSRWLockExclusive(AWSSRW_TO_WINDOWS(lock));

    return AWS_OP_SUCCESS;
}

AWS_EXTERN_C_END

#endif /* AWS_COMMON_WINDOWS_RW_LOCK_INL */
