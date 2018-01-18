/*
* Copyright 2010 - 2018 Amazon.com, Inc. or its affiliates.All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
*  http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file.This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied.See the License for the specific language governing
* permissions and limitations under the License.
*/

#include <aws/common/thread.h>

static DWORD thread_wrapper_fn(LPVOID arg) {
    struct aws_thread *thread = (struct aws_thread *)arg;
    thread->thread_wrapper.func(thread->thread_wrapper.arg);

    return 0;
}

int aws_thread_init(struct aws_thread *thread, struct aws_allocator *allocator) {
    thread->thread_handle = 0;
    thread->thread_wrapper.func = 0;
    thread->thread_wrapper.arg = 0;
    thread->thread_id = 0;
    thread->allocator = allocator;

    return AWS_ERROR_SUCCESS;
}

int aws_thread_create(struct aws_thread *thread, void(*func)(void *arg), void *context, struct aws_thread_options *options) {

    SIZE_T stack_size = 0;

    if (options && options->stack_size > 0) {
        stack_size = (SIZE_T)options->stack_size;
    }

    thread->thread_wrapper.func = func;
    thread->thread_wrapper.arg = context;
    thread->thread_handle = CreateThread(0, stack_size, thread_wrapper_fn, (LPVOID)thread, 0, &thread->thread_id);

    if (!thread->thread_handle) {
        return aws_raise_error(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE);
    }

    return AWS_ERROR_SUCCESS;
}

uint64_t aws_thread_get_id(struct aws_thread *thread) {
    return thread->thread_id;
}

int aws_thread_detach(struct aws_thread *thread) {

    if (thread->thread_handle) {
        CloseHandle(thread->thread_handle);
        thread->thread_handle = 0;
    }
    return AWS_ERROR_SUCCESS;
}

int aws_thread_join(struct aws_thread *thread) {

    WaitForSingleObject(thread->thread_handle, INFINITE);

    return AWS_ERROR_SUCCESS;
}

void aws_thread_clean_up(struct aws_thread *thread) {
    aws_thread_detach(thread);
}

uint64_t aws_thread_current_thread_id() {
    return (uint64_t)GetCurrentThreadId();
}
