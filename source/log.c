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

#include <stdio.h>

#include <aws/common/common.h>
#include <aws/common/log.h>
#include <aws/common/memory_pool.h>
#include <aws/common/atomic.h>

struct aws_log_context *global_log_list;
AWS_THREAD_LOCAL struct aws_log_context thread_local_log_context;

void aws_log(enum aws_log_level level, const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    vsprintf(???, fmt, args);
    va_end(args);
}

const char *aws_log_level_to_string(enum aws_log_level level) {
    switch (level) {
        case AWS_LOG_LEVEL_OFF:     return "AWS_LOG_LEVEL_OFF";
        case AWS_LOG_LEVEL_FATAL:   return "AWS_LOG_LEVEL_FATAL";
        case AWS_LOG_LEVEL_ERROR:   return "AWS_LOG_LEVEL_ERROR";
        case AWS_LOG_LEVEL_WARN:    return "AWS_LOG_LEVEL_WARN";
        case AWS_LOG_LEVEL_TRACE:   return "AWS_LOG_LEVEL_TRACE";
        default: return NULL;
    }
}

void aws_log_process() {
}

void aws_init_logging(struct aws_allocator *alloc, int memory_pool_element_count) {
    aws_memory_pool_init(&thread_local_log_context.message_pool, alloc, sizeof(struct aws_log_message), memory_pool_element_count);
    void *previous_head = aws_atomic_cas_ptr(&global_log_list, global_log_list, &thread_local_log_context);
    thread_local_log_context.next = (struct aws_log_context *)previous_head;
}

void aws_shutdown_logging() {
    aws_memory_pool_clean_up(&thread_local_log_context.message_pool);
}
