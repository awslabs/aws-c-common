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

#include <aws/common/mutex.h>

int aws_mutex_init(struct aws_mutex *mutex, struct aws_allocator *allocator) {
    mutex->allocator = allocator;
    InitializeSRWLock(&mutex->mutex_handle);
    return AWS_OP_SUCCESS;
}

/* turn off unused named parameter warning on msvc.*/
#ifdef _MSC_VER
#pragma warning(push)
#pragma warning(disable : 4100)
#endif

void aws_mutex_clean_up(struct aws_mutex *mutex) {
}

int aws_mutex_lock(struct aws_mutex *mutex) {
    AcquireSRWLockExclusive(&mutex->mutex_handle);
    return AWS_OP_SUCCESS;
}

int aws_mutex_try_lock(struct aws_mutex *mutex) {
    BOOL res = TryAcquireSRWLockExclusive(&mutex->mutex_handle);

    if (!res) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
}

int aws_mutex_unlock(struct aws_mutex *mutex) {
    ReleaseSRWLockExclusive(&mutex->mutex_handle);
    return AWS_OP_SUCCESS;
}
