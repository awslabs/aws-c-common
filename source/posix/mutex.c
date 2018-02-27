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
#include <errno.h>

void aws_mutex_clean_up(struct aws_mutex *mutex) {
    pthread_mutex_destroy(&mutex->mutex_handle);
}

static int convert_and_raise_error_code (int error_code) {
    switch (error_code) {
        case 0:
            return AWS_OP_SUCCESS;
        case EINVAL:
            return aws_raise_error(AWS_ERROR_MUTEX_NOT_INIT);
        case EBUSY:
            return aws_raise_error(AWS_ERROR_MUTEX_TIMEOUT);
        case EPERM:
            return aws_raise_error(AWS_ERROR_MUTEX_CALLER_NOT_OWNER);
        case ENOMEM:
            return aws_raise_error(AWS_ERROR_OOM);
        case EDEADLK:
            return aws_raise_error(AWS_ERROR_THREAD_DEADLOCK_DETECTED);
        default:
            return aws_raise_error(AWS_ERROR_MUTEX_FAILED);
    }
}

int aws_mutex_init(struct aws_mutex *mutex, struct aws_allocator *allocator) {

    mutex->allocator = allocator;
    pthread_mutexattr_t attr;
    int err_code = pthread_mutexattr_init(&attr);
    int return_code = AWS_OP_SUCCESS;

    if(!err_code) {
        if((err_code = pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_NORMAL)) ||
            (err_code = pthread_mutex_init(&mutex->mutex_handle, &attr))) {
            return_code = convert_and_raise_error_code(err_code);
        }
        pthread_mutexattr_destroy(&attr);
    }
    else {
        return_code = convert_and_raise_error_code(err_code);
    }

    return return_code;
}

int aws_mutex_lock(struct aws_mutex *mutex) {

    return convert_and_raise_error_code(pthread_mutex_lock(&mutex->mutex_handle));
}

int aws_mutex_try_lock(struct aws_mutex *mutex) {

    return convert_and_raise_error_code(pthread_mutex_trylock(&mutex->mutex_handle));
}

int aws_mutex_unlock(struct aws_mutex *mutex) {

    return convert_and_raise_error_code(pthread_mutex_unlock(&mutex->mutex_handle));
}

