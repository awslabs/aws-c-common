/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/rw_lock.h>
#include <aws/common/thread.h>

#include <windows.h>

#include <synchapi.h>

/* Convert a string from a macro to a wide string */
#define WIDEN2(s) L## #s
#define WIDEN(s) WIDEN2(s)

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

/* Check for functions that don't exist on ancient windows */
static aws_thread_once s_check_functions_once = INIT_ONCE_STATIC_INIT;

typedef BOOLEAN WINAPI TryAcquireSRWLockExclusive_fn(PSRWLOCK SRWLock);
static TryAcquireSRWLockExclusive_fn *s_TryAcquireSRWLockExclusive;
typedef BOOLEAN WINAPI TryAcquireSRWLockShared_fn(PSRWLOCK SRWLock);
static TryAcquireSRWLockShared_fn *s_TryAcquireSRWLockShared;

static void s_check_try_lock_function(void *user_data) {
    (void)user_data;

    s_TryAcquireSRWLockExclusive = (TryAcquireSRWLockExclusive_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "TryAcquireSRWLockExclusive");
    s_TryAcquireSRWLockShared = (TryAcquireSRWLockShared_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "TryAcquireSRWLockShared");
}

int aws_rw_lock_try_rlock(struct aws_rw_lock *lock) {
    (void)lock;
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_functions_once, s_check_try_lock_function, NULL);

    if (!s_TryAcquireSRWLockShared) {
        return aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
    }

    if (s_TryAcquireSRWLockShared(AWSSRW_TO_WINDOWS(lock))) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_rw_lock_try_wlock(struct aws_rw_lock *lock) {
    (void)lock;
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_functions_once, s_check_try_lock_function, NULL);

    if (!s_TryAcquireSRWLockExclusive) {
        return aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
    }

    if (s_TryAcquireSRWLockExclusive(AWSSRW_TO_WINDOWS(lock))) {
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
