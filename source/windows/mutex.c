/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/mutex.h>

#include <Windows.h>

int aws_mutex_init(struct aws_mutex *mutex) {
    /* Ensure our mutex and Windows' mutex are the same size */
    AWS_STATIC_ASSERT(sizeof(SRWLOCK) == sizeof(mutex->mutex_handle));

    InitializeSRWLock(AWSMUTEX_TO_WINDOWS(mutex));
    mutex->initialized = true;
    return AWS_OP_SUCCESS;
}

/* turn off unused named parameter warning on msvc.*/
#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4100)
#endif

void aws_mutex_clean_up(struct aws_mutex *mutex) {
    AWS_PRECONDITION(mutex);
    AWS_ZERO_STRUCT(*mutex);
}

int aws_mutex_lock(struct aws_mutex *mutex) {
    AWS_PRECONDITION(mutex && mutex->initialized);
    AcquireSRWLockExclusive(AWSMUTEX_TO_WINDOWS(mutex));
    return AWS_OP_SUCCESS;
}

int aws_mutex_try_lock(struct aws_mutex *mutex) {
    AWS_PRECONDITION(mutex && mutex->initialized);
    BOOL res = TryAcquireSRWLockExclusive(AWSMUTEX_TO_WINDOWS(mutex));

    /*
     * Per Windows documentation, a return value of zero indicates a failure to acquire the lock.
     */
    if (!res) {
        return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
    }

    return AWS_OP_SUCCESS;
}

int aws_mutex_unlock(struct aws_mutex *mutex) {
    AWS_PRECONDITION(mutex && mutex->initialized);
    ReleaseSRWLockExclusive(AWSMUTEX_TO_WINDOWS(mutex));
    return AWS_OP_SUCCESS;
}

#ifdef _MSC_VER
#    pragma warning(pop)
#endif
