/*
* Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <stdlib.h>

/* turn off unused named parameter warning on msvc.*/
#ifdef _MSC_VER 
#pragma warning( push )
#pragma warning( disable : 4100)
#endif

void *default_malloc(struct aws_allocator *allocator, size_t size) {
    return malloc(size);
}

void default_free(struct aws_allocator *allocator, void *ptr) {
    free(ptr);
}

static struct aws_allocator default_allocator = {
        .mem_acquire = default_malloc,
        .mem_release = default_free
};

struct aws_allocator *aws_default_allocator() {
    return &default_allocator;
}

void *aws_mem_acquire(struct aws_allocator *allocator, size_t size) {
    void * mem = allocator->mem_acquire(allocator, size);
    if (!mem) aws_raise_error(AWS_ERROR_OOM);
    return mem;
}

void aws_mem_release(struct aws_allocator *allocator, void *ptr) {
    allocator->mem_release(allocator, ptr);
}

static int8_t error_strings_loaded = 0;

static struct aws_error_info errors[] = {
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_SUCCESS, "success", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_OOM, "out-of-memory", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_UNKNOWN, "unknown error", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_SHORT_BUFFER, "Insufficient data in input buffer", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_OVERFLOW_DETECTED, "fixed size value overflow was detected", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_INVALID_BUFFER_SIZE, "invalid buffer size", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_INVALID_HEX_STR, "invalid hex string", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_INVALID_BASE64_STR, "invalid base64 string", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_INVALID_INDEX, "invalid index for list access", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_INVALID_SETTINGS, "invalid thread settings", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_INSUFFICIENT_RESOURCE, "thread, insufficient resources", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_NO_PERMISSIONS, "insufficient permissions for thread operation", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_NOT_JOINABLE, "thread not join-able", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_NO_SUCH_THREAD_ID, "no such thread id", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_THREAD_DEADLOCK_DETECTED, "deadlock detected", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_MUTEX_NOT_INIT, "mutex not initialized", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_MUTEX_TIMEOUT, "mutex operation timed out", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_MUTEX_CALLER_NOT_OWNER, "the caller of a mutex operation was not the owner", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_MUTEX_FAILED, "mutex operation failed", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_COND_VARIABLE_INIT_FAILED, "condition variable initialization failed.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_COND_VARIABLE_TIMED_OUT, "condition variable wait timed out.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN, "condition variable unknown error.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_CLOCK_FAILURE, "clock get ticks operation failed", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_LIST_EMPTY, "empty list", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_DEST_COPY_TOO_SMALL, "destination of copy is too small", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE, "a requested operation on a list would exceed it's max size.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK, "attempt to shrink a list in static mode", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_PRIORITY_QUEUE_FULL, "attempt to add items to a full preallocated queue in static mode.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_PRIORITY_QUEUE_EMPTY, "attempt to pop an item from an empty queue.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_TASK_SCHEDULER_NO_TASKS, "no tasks scheduled available.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_TASK_SCHEDULER_NO_READY_TASKS, "none of the tasks scheduled is due to run now.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(AWS_ERROR_HASHTBL_ITEM_NOT_FOUND, "Item not found in hash table", AWS_LIB_NAME)
};

static struct aws_error_info_list list = {
       .error_list = errors,
        .count = sizeof(errors) / sizeof(struct aws_error_info),
};

void aws_load_error_strings(void) {
    if(!error_strings_loaded) {
        error_strings_loaded = 1;
        aws_register_error_info(&list);
    }
}
