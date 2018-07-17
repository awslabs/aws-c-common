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
#include <aws/common/mutex.h>

aws_log_report_callback global_log_report_callback;
struct aws_mutex global_log_list_mutex = AWS_MUTEX_INIT;
struct aws_log_context *global_log_list;

AWS_THREAD_LOCAL struct aws_log_context thread_local_log_context;

static struct aws_log_message *aws_log_acquire_message_internal() {
    void *mem = aws_memory_pool_acquire(&thread_local_log_context.message_pool);
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    return msg;
}

void aws_log_set_reporting_callback(aws_log_report_callback report_callback) {
    global_log_report_callback = report_callback;
}

int aws_log(enum aws_log_level level, const char *fmt, ...) {
    (void)level;

    if (!thread_local_log_context.running)
        return AWS_OP_ERR;

    /* Automically grab and release all messages on the `delete_list` whenever present. */
    struct aws_log_message* delete_list;
    do {
        delete_list = thread_local_log_context.delete_list;
    } while (aws_atomic_cas_ptr(&thread_local_log_context.delete_list, delete_list, NULL));

    while (delete_list) {
        struct aws_log_message *next = delete_list->next;
        aws_memory_pool_release(&thread_local_log_context.message_pool, delete_list);
        delete_list = next;
    }

    /* Acquire memory for the new message. */
    void* mem = aws_memory_pool_acquire(&thread_local_log_context.message_pool);

    /* Format the message. */
    va_list args;
    va_start(args, fmt);
    vsnprintf((char *)mem, thread_local_log_context.max_message_len, fmt, args);
    va_end(args);

    /* Push formatted message onto this thread's message list. Will be picked up later and
    processed by the logging thread in `process()`, and handed to a user callback set by
    `aws_log_set_reporting_callback`. */
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    do {
        msg->next = thread_local_log_context.message_list;
    } while (!aws_atomic_cas_ptr(&thread_local_log_context.message_list, msg->next, msg));

    return AWS_OP_SUCCESS;
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

int aws_log_process() {
    aws_log_report_callback cb = global_log_report_callback;
    if (!cb || !global_log_list)
        return AWS_OP_ERR;

    struct aws_log_context *log_list = global_log_list;
    struct aws_log_context *sentinel = log_list;
    do {
        struct aws_log_context *next = log_list->next;

        /* Grab the message list, automically. */
        struct aws_log_message* msg_list;
        do {
            msg_list = log_list->message_list;
        } while (aws_atomic_cas_ptr(&log_list->message_list, msg_list, NULL));

        /* Reverse the list to preserve user submitted order, for reporting. */
        struct aws_log_message *last_msg = msg_list;
        AWS_SINGLY_LIST_REVERSE(struct aws_log_message, msg_list);
        /* AWS_ASSERT(last_msg->next == NULL); */

        /* Report logs to the user. */
        struct aws_log_message *msg = msg_list;
        while (msg) {
            cb((const char*)msg->memory);
            msg = msg->next;
        }

        /* Release all messages to the thread local memory pool by appending to the `delete_list`. */
        do {
            last_msg->next = thread_local_log_context.delete_list;
        } while (aws_atomic_cas_ptr(&thread_local_log_context.delete_list, last_msg->next, msg_list));

        /* Remove dead threads. */
        if (!log_list->running) {
            AWS_DOUBLY_LIST_REMOVE(&thread_local_log_context);
            aws_memory_pool_clean_up(&thread_local_log_context.message_pool);
        }

        log_list = next;
    } while (log_list != sentinel);

    return AWS_OP_SUCCESS;
}

int aws_log_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count) {
    thread_local_log_context.max_message_len = max_message_len;
    int ret = aws_memory_pool_init(&thread_local_log_context.message_pool, alloc, sizeof(struct aws_log_message), memory_pool_message_count);
    if (ret)
        return AWS_OP_ERR;
    AWS_DOUBLY_LIST_INIT(&thread_local_log_context);

    /* Insert thread local log info struct onto the global doubly linked list used by
    the logging thread. */
    aws_mutex_lock(&global_log_list_mutex);
    if (!global_log_list) {
        global_log_list = &thread_local_log_context;
    } else {
        AWS_DOUBLY_LIST_INSERT_BEFORE(global_log_list, &thread_local_log_context);
    }
    aws_mutex_unlock(&global_log_list_mutex);

    thread_local_log_context.running = 1;

    return AWS_OP_SUCCESS;
}

void aws_log_clean_up() {
    /* Mark for removal from `global_log_list` by the logging thread. */
    thread_local_log_context.running = 0;
}
