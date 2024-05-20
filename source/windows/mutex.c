/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#include <windows.h>

/* Convert a string from a macro to a wide string */
#define WIDEN2(s) L## #s
#define WIDEN(s) WIDEN2(s)

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
/* Check for functions that don't exist on ancient windows */
static aws_thread_once s_check_functions_once = INIT_ONCE_STATIC_INIT;

typedef BOOLEAN WINAPI TryAcquireSRWLockExclusive_fn(PSRWLOCK SRWLock);
static TryAcquireSRWLockExclusive_fn *s_TryAcquireSRWLockExclusive;

static void s_check_try_lock_function(void *user_data) {
    (void)user_data;

    s_TryAcquireSRWLockExclusive = (TryAcquireSRWLockExclusive_fn *)GetProcAddress(
        GetModuleHandleW(WIDEN(WINDOWS_KERNEL_LIB) L".dll"), "TryAcquireSRWLockExclusive");
}

int aws_mutex_try_lock(struct aws_mutex *mutex) {
    AWS_PRECONDITION(mutex && mutex->initialized);
    /* Check for functions that don't exist on ancient Windows */
    aws_thread_call_once(&s_check_functions_once, s_check_try_lock_function, NULL);

    if (!s_TryAcquireSRWLockExclusive) {
        return aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
    }
    BOOL res = s_TryAcquireSRWLockExclusive(AWSMUTEX_TO_WINDOWS(mutex));
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
