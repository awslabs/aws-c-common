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

struct thread_wrapper {
    struct aws_allocator *allocator;
    void(*func)(void *arg);
    void *arg;
};

static DWORD thread_wrapper_fn(LPVOID arg) {
    struct thread_wrapper *thread_wrapper = (struct thread_wrapper *)arg;
    thread_wrapper->func(thread_wrapper->arg);
    aws_mem_release(thread_wrapper->allocator, thread_wrapper);
    return 0;
}

int aws_thread_init(struct aws_thread *thread, struct aws_allocator *allocator) {
    thread->thread_handle = 0;    
    thread->thread_id = 0;
    thread->allocator = allocator;

    return AWS_OP_SUCCESS;
}

int aws_thread_create(struct aws_thread *thread, void(*func)(void *arg), void *context, struct aws_thread_options *options) {

    SIZE_T stack_size = 0;

    if (options && options->stack_size > 0) {
        stack_size = (SIZE_T)options->stack_size;
    }

    struct thread_wrapper *thread_wrapper = (struct thread_wrapper *)aws_mem_acquire(thread->allocator, sizeof(struct thread_wrapper));
    thread_wrapper->allocator = thread->allocator;
    thread_wrapper->arg = context;
    thread_wrapper->func = func;
    thread->thread_handle = CreateThread(0, stack_size, thread_wrapper_fn, (LPVOID)thread_wrapper, 0, &thread->thread_id);

    if (!thread->thread_handle) {
        return aws_raise_error(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE);
    }

    return AWS_OP_SUCCESS;
}

uint64_t aws_thread_get_id(struct aws_thread *thread) {
    return thread->thread_id;
}

int aws_thread_detach(struct aws_thread *thread) {

    if (thread->thread_handle) {
        CloseHandle(thread->thread_handle);
        thread->thread_handle = 0;
    }
    return AWS_OP_SUCCESS;
}

int aws_thread_join(struct aws_thread *thread) {

    WaitForSingleObject(thread->thread_handle, INFINITE);

    return AWS_OP_SUCCESS;
}

void aws_thread_clean_up(struct aws_thread *thread) {
    aws_thread_detach(thread);
}

uint64_t aws_thread_current_thread_id() {
    return (uint64_t)GetCurrentThreadId();
}

void aws_thread_current_sleep(uint64_t nanos) {
    /* We don't really have a better option here for windows that isn't super complex AND we don't have a use case
     * yet where we should have sleeps anywhere other than for context switches and testing. When that time arises
     * put the effort in here. */
    Sleep(nanos / 1000000);
}
