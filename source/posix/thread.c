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

#include <aws/common/thread.h>

#include <limits.h>
#include <errno.h>
#include <time.h>
#include <assert.h>

static struct aws_thread_options default_options = {
        /* this will make sure platform default stack size is used. */
        .stack_size = 0
};

struct thread_wrapper {
    struct aws_allocator *allocator;
    void(*func)(void *arg);
    void *arg;
};

static void *thread_fn(void *arg) {
    struct thread_wrapper wrapper = *(struct thread_wrapper *)arg;
    aws_mem_release(wrapper.allocator, arg);

    wrapper.func(wrapper.arg);
    return NULL;
}

const struct aws_thread_options *aws_default_thread_options(void) {
    return &default_options;
}

void aws_thread_clean_up (struct aws_thread *thread) {
    if(thread->detach_state == AWS_THREAD_JOINABLE) {
        pthread_detach(thread->thread_id);
    }
}

int aws_thread_init (struct aws_thread *thread, struct aws_allocator *allocator) {
    thread->allocator = allocator;
    thread->thread_id = 0;
    thread->detach_state = AWS_THREAD_NOT_CREATED;

    return AWS_OP_SUCCESS;
}

int aws_thread_launch (struct aws_thread *thread, void(*func)(void *arg), void *arg, struct aws_thread_options *options) {

    pthread_attr_t attributes;
    pthread_attr_t *attributes_ptr = NULL;
    int attr_return = 0;

    if(options) {
        attr_return = pthread_attr_init(&attributes);

        if(attr_return) {
            goto cleanup;
        }

        attributes_ptr = &attributes;

        if(options->stack_size > PTHREAD_STACK_MIN ) {
            attr_return = pthread_attr_setstacksize(attributes_ptr, options->stack_size);

            if(attr_return) {
                goto cleanup;
            }
        }
    }
    
    int allocation_failed = 0;
    struct thread_wrapper *wrapper = (struct thread_wrapper *)aws_mem_acquire(thread->allocator, sizeof(struct thread_wrapper));
    
    if(!wrapper) {
        allocation_failed = 1;
        goto cleanup;
    }

    wrapper->allocator = thread->allocator;
    wrapper->func = func;
    wrapper->arg = arg;
    attr_return = pthread_create(&thread->thread_id, attributes_ptr, thread_fn, (void *)wrapper);

    if(attr_return) {
        goto cleanup;
    }

    thread->detach_state = AWS_THREAD_JOINABLE;

    cleanup:
    if(attributes_ptr) {
        pthread_attr_destroy(attributes_ptr);
    }

    if(attr_return == EINVAL) {
        return aws_raise_error(AWS_ERROR_THREAD_INVALID_SETTINGS);
    }

    if(attr_return == EAGAIN)
        return aws_raise_error(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE);

    if(attr_return == EPERM) {
        return aws_raise_error(AWS_ERROR_THREAD_NO_PERMISSIONS);
    }

    if(allocation_failed || attr_return == ENOMEM) {
        return aws_raise_error(AWS_ERROR_OOM);
    }

    return AWS_OP_SUCCESS;
}


uint64_t aws_thread_get_id (struct aws_thread *thread) {
    return (uint64_t)thread->thread_id;
}

aws_thread_detach_state aws_thread_get_detach_state(struct aws_thread *thread) {
    return thread->detach_state;
}

int aws_thread_join(struct aws_thread *thread) {
    if(thread->detach_state == AWS_THREAD_JOINABLE) {
        int err_no = pthread_join(thread->thread_id, 0);

        if (err_no) {
            if (err_no == EINVAL) {
                return aws_raise_error(AWS_ERROR_THREAD_NOT_JOINABLE);
            } else if (err_no == ESRCH) {
                return aws_raise_error(AWS_ERROR_THREAD_NO_SUCH_THREAD_ID);
            } else if (err_no == EDEADLK) {
                return aws_raise_error(AWS_ERROR_THREAD_DEADLOCK_DETECTED);
            }
        }

        thread->detach_state = AWS_THREAD_JOIN_COMPLETED;
    }

    return AWS_OP_SUCCESS;
}

uint64_t aws_thread_current_thread_id() {
    return (uint64_t)pthread_self();
}

void aws_thread_current_sleep(uint64_t nanos) {
    uint64_t seconds = nanos / 1000000000;
    uint64_t nano = nanos % 1000000000;

    struct timespec tm = {
        .tv_sec = seconds,
        .tv_nsec = nano,
    };
    struct timespec output;

    nanosleep(&tm, &output);
}


