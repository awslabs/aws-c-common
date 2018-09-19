#include <aws/common/atomics.h>
#ifndef AWS_COMMON_POSIX_RW_LOCK_INL
#define AWS_COMMON_POSIX_RW_LOCK_INL

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

#include <aws/common/posix/common.inl>

#ifdef __cplusplus
extern "C" {
#endif

AWS_STATIC_IMPL int aws_rw_lock_init(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_init(&lock->lock_handle, NULL));
}

AWS_STATIC_IMPL void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    pthread_rwlock_destroy(&lock->lock_handle);
}

AWS_STATIC_IMPL int aws_rw_lock_rlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_rdlock(&lock->lock_handle));
}

AWS_STATIC_IMPL int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_wrlock(&lock->lock_handle));
}

AWS_STATIC_IMPL int aws_rw_lock_try_rlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_tryrdlock(&lock->lock_handle));
}

AWS_STATIC_IMPL int aws_rw_lock_try_wlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_trywrlock(&lock->lock_handle));
}

AWS_STATIC_IMPL int aws_rw_lock_runlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_unlock(&lock->lock_handle));
}

AWS_STATIC_IMPL int aws_rw_lock_wunlock(struct aws_rw_lock *lock) {

    return aws_private_convert_and_raise_error_code(pthread_rwlock_unlock(&lock->lock_handle));
}

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_POSIX_RW_LOCK_INL */
