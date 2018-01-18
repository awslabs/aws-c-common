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


static void *thread_wrapper_fn (void *arg_pass) {
    struct aws_thread_wrapper *wrapper = (struct aws_thread_wrapper *)arg_pass;
    wrapper->func(wrapper->arg);
    return 0;
}

void aws_thread_clean_up (struct aws_thread *thread) {
    /* this likely won't do anything if the thread has already terminated, but it shouldn't hurt to send a cancel signal just in case.
       should we join here? */
    pthread_cancel(thread->thread_id);
}

int aws_thread_init (struct aws_thread *thread, struct aws_allocator *allocator) {
    thread->allocator = allocator;
    thread->thread_id = 0;

    return AWS_ERROR_SUCCESS;
}

int aws_thread_create (struct aws_thread *thread, void(*func)(void *arg), void *context, struct aws_thread_options *options) {

    pthread_attr_t attributes;
    pthread_attr_t *attributes_ptr = 0;
    int attr_return = 0;

    if(options) {
        attr_return = pthread_attr_init(&attributes);

        if(attr_return) {
            goto cleanup;
        }

        attributes_ptr = &attributes;
        int detach_state = 0;

        if(options->detach_state == AWS_THREAD_JOINABLE) {
            detach_state = PTHREAD_CREATE_JOINABLE;
        }
        else if(options->detach_state == AWS_THREAD_DETACHED) {
            detach_state = PTHREAD_CREATE_DETACHED;
        }

        if(detach_state != 0) {
            attr_return = pthread_attr_setdetachstate(attributes_ptr, detach_state);

            if(attr_return) {
                goto cleanup;
            }
        }

        if(options->stack_size > PTHREAD_STACK_MIN ) {
            attr_return = pthread_attr_setstacksize(attributes_ptr, options->stack_size);

            if(attr_return) {
                goto cleanup;
            }
        }
    }

    thread->thread_wrapper.func = func;
    thread->thread_wrapper.arg = context;
    attr_return = pthread_create(&thread->thread_id, attributes_ptr, thread_wrapper_fn, &thread->thread_wrapper);

    if(attr_return) {
        goto cleanup;
    }

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

    if(attr_return == ENOMEM) {
        return AWS_ERROR_OOM;
    }

    return AWS_ERROR_SUCCESS;
}


uint64_t aws_thread_get_id (struct aws_thread *thread) {
    return (uint64_t)thread->thread_id;
}

int aws_thread_detach(struct aws_thread *thread) {
    int err_no = pthread_detach(thread->thread_id);

    if (err_no) {
        if (err_no == EINVAL) {
            return aws_raise_error(AWS_ERROR_THREAD_NOT_JOINABLE);
        }
        else if (err_no == ESRCH) {
            return aws_raise_error(AWS_ERROR_THREAD_NO_SUCH_THREAD_ID);
        }
    }

    return AWS_ERROR_SUCCESS;
}

int aws_thread_join(struct aws_thread *thread) {
    int err_no = pthread_join(thread->thread_id, 0);

    if (err_no) {
        if (err_no == EINVAL) {
            return aws_raise_error(AWS_ERROR_THREAD_NOT_JOINABLE);
        }
        else if (err_no == ESRCH) {
            return aws_raise_error(AWS_ERROR_THREAD_NO_SUCH_THREAD_ID);
        }
        else if (err_no == EDEADLK) {
            return aws_raise_error(AWS_ERROR_THREAD_DEADLOCK_DETECTED);
        }
    }

    return AWS_ERROR_SUCCESS;
}

uint64_t aws_thread_current_thread_id() {
    return (uint64_t)pthread_self();
}

