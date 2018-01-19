#ifndef AWS_COMMON_THREAD_H_
#define AWS_COMMON_THREAD_H_

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

#include <aws/common/common.h>
#include <stdint.h>

#ifdef _WIN32
#include <Windows.h>
#else
#include <pthread.h>
#endif

typedef enum aws_thread_detach_state {
    AWS_THREAD_JOINABLE = 1,
    AWS_THREAD_DETACHED = 2,
} aws_thread_detach_state;

struct aws_thread_options {
    aws_thread_detach_state detach_state;
    size_t stack_size;
};

struct aws_thread {
    struct aws_allocator *allocator;

#ifdef _WIN32
    HWND thread_handle;
    DWORD thread_id;
#else
    pthread_t thread_id;
#endif
};

#ifdef __cplusplus
extern "C" {
#endif
/**
 * Initializes a new platform specific thread object struct (not the os-level thread itself).
 */
AWS_COMMON_API int aws_thread_init(struct aws_thread *thread, struct aws_allocator *allocator);

/**
 * Creates an OS level thread and associates it with func. context will be passed to func when it is executed.
 * options will be applied to the thread if they are applicable for the platform.
 */
AWS_COMMON_API int aws_thread_create(struct aws_thread *thread, void(*func)(void *arg),
                                                      void *context, struct aws_thread_options *options);

/**
 * Gets the id of thread
 */
AWS_COMMON_API uint64_t aws_thread_get_id(struct aws_thread *thread);

/**
 * Detaches thread from this instance of thread. You probably want to call aws_core_thread_destroy()
 * immediately afterwards.
 */
AWS_COMMON_API int aws_thread_detach(struct aws_thread *thread);

/**
 * Joins the calling thread to a thread instance. Returns when thread is finished.
 */
AWS_COMMON_API int aws_thread_join(struct aws_thread *thread);

/**
 * Cleans up the thread handle, if thread is still running, it will continue doing so.
 */
AWS_COMMON_API void aws_thread_clean_up(struct aws_thread *thread);

/**
 * returns the thread id of the calling thread.
 */
AWS_COMMON_API uint64_t aws_thread_current_thread_id();

/**
 * Sleeps the current thread by millis.
 */
AWS_COMMON_API void aws_thread_current_sleep(uint32_t millis);

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_THREAD_H_ */
