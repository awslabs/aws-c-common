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

#include <aws/common/atomic.h>
#include <aws/common/common.h>
#include <aws/common/log.h>
#include <aws/common/memory_pool.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

static void aws_log_default_report_function_internal(const char* log_message) {
    (void)log_message;
}

int global_log_thread_count;
aws_log_report_callback global_log_report_callback = aws_log_default_report_function_internal;
struct aws_mutex global_log_list_mutex = AWS_MUTEX_INIT;
struct aws_log_context *global_log_list;

AWS_THREAD_LOCAL struct aws_log_context *thread_local_log_context;

static struct aws_log_message *aws_log_acquire_message_internal() {
    void *mem = aws_memory_pool_acquire(&thread_local_log_context->message_pool);
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    return msg;
}

void aws_log_set_reporting_callback(aws_log_report_callback report_callback) {
    if (report_callback) {
        global_log_report_callback = report_callback;
    } else {
        global_log_report_callback = aws_log_default_report_function_internal;
    }
}

int aws_vlog(enum aws_log_level level, const char *fmt, va_list va_args) {
    (void)level;

    if (!thread_local_log_context->running) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    /* Atomically grab and release all messages on the `delete_list` whenever present. */
    struct aws_log_message* delete_list;
    do {
        delete_list = thread_local_log_context->delete_list;
    } while (!aws_atomic_compare_exchange_ptr(&thread_local_log_context->delete_list, delete_list, NULL));

    while (delete_list) {
        struct aws_log_message *next = delete_list->next;
        aws_memory_pool_release(&thread_local_log_context->message_pool, delete_list);
        delete_list = next;
    }

    /* Acquire memory for the new message. */
    void *mem = aws_memory_pool_acquire(&thread_local_log_context->message_pool);
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    char *msg_data = (char*)(msg + 1);

    /* Format the message. */
    vsnprintf((char *)msg_data, thread_local_log_context->max_message_len, fmt, va_args);

    /* Push formatted message onto this thread's message list. Will be picked up later and
    processed by the logging thread in `aws_log_flush()`, and handed to a user callback set by
    `aws_log_set_reporting_callback`. */
    do {
        msg->next = thread_local_log_context->message_list;
    } while (!aws_atomic_compare_exchange_ptr(&thread_local_log_context->message_list, msg->next, msg));

    return AWS_OP_SUCCESS;
}

int aws_log(enum aws_log_level level, const char *fmt, ...) {
    va_list va_args;
    va_start(va_args, fmt);
    int ret = aws_vlog(level, fmt, va_args);
    va_end(va_args);
    return ret;
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

int aws_log_flush() {
    struct aws_log_context *log_list = global_log_list;
    struct aws_log_context *sentinel = log_list;
    do {
        struct aws_log_context *next = log_list->next;

        /* Grab the message list, atomically. */
        struct aws_log_message* msg_list;
        do {
            msg_list = log_list->message_list;
        } while (!aws_atomic_compare_exchange_ptr(&log_list->message_list, msg_list, NULL));

        /* Reverse the list to preserve user submitted order, for reporting. */
        if (msg_list) {
            struct aws_log_message *last_msg = msg_list;
            AWS_SINGLY_LIST_REVERSE(struct aws_log_message, msg_list);
            /* AWS_ASSERT(last_msg->next == NULL); */

            /* Report logs to the user. */
            struct aws_log_message *msg = msg_list;
            while (msg) {
                char *msg_data = (char*)(msg + 1);
                global_log_report_callback(msg_data);
                msg = msg->next;
            }

            /* Release all messages to the thread local memory pool by appending to the `delete_list`. */
            do {
                last_msg->next = thread_local_log_context->delete_list;
            } while (!aws_atomic_compare_exchange_ptr(&thread_local_log_context->delete_list, last_msg->next, msg_list));
        }

        log_list = next;
    } while (log_list != sentinel);

    return AWS_OP_SUCCESS;
}

int aws_log_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count) {
    if (aws_atomic_get_ptr(&thread_local_log_context)) {
        aws_raise_error(AWS_ERROR_LOG_DOUBLE_INITIALIZE);
        return AWS_OP_ERR;
    }

    aws_atomic_add(&global_log_thread_count, 1);
    aws_atomic_set_ptr(&thread_local_log_context, alloc->mem_acquire(alloc, sizeof(struct aws_log_context)));
    if (!thread_local_log_context) {
        aws_raise_error(AWS_ERROR_OOM);
        return AWS_OP_ERR;
    }

    memset(thread_local_log_context, 0, sizeof(*thread_local_log_context));
    thread_local_log_context->running = 1;
    thread_local_log_context->max_message_len = max_message_len;
    thread_local_log_context->alloc = alloc;
    int ret = aws_memory_pool_init(&thread_local_log_context->message_pool, alloc, sizeof(struct aws_log_message) + max_message_len, memory_pool_message_count);
    if (ret) {
        aws_raise_error(AWS_ERROR_OOM);
        return AWS_OP_ERR;
    }
    AWS_DOUBLY_LIST_INIT(thread_local_log_context);

    /* Insert thread local log info struct onto the global doubly linked list used by
    the logging thread. */
    aws_mutex_lock(&global_log_list_mutex);
    if (!global_log_list) {
        global_log_list = thread_local_log_context;
    } else {
        AWS_DOUBLY_LIST_INSERT_BEFORE(global_log_list, thread_local_log_context);
    }
    aws_mutex_unlock(&global_log_list_mutex);


    return AWS_OP_SUCCESS;
}

int aws_log_clean_up() {
    if (aws_atomic_get(&global_log_thread_count) == 0) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    struct aws_log_context *context;
    do {
        context = thread_local_log_context;
    } while (!aws_atomic_compare_exchange_ptr(&thread_local_log_context, context, NULL));

    context->running = 0;

    /* Perform final cleanup if this is the last log thread. */
    aws_mutex_lock(&global_log_list_mutex);
    if (aws_atomic_add(&global_log_thread_count, -1) == 1) {
        struct aws_log_context *log_list = global_log_list;
        global_log_list = NULL;
        aws_mutex_unlock(&global_log_list_mutex);

        /* Make sure all the other log threads have been joined and remove dead threads. */
        struct aws_log_context *sentinel = log_list;
        do {
            struct aws_log_context *next = log_list->next;

            /* Remove dead threads. Log any leftover messages. Cleanup leftover message pool memory. */
            if (!log_list->running) {
                struct aws_log_message *delete_list = log_list->message_list;
                while (delete_list) {
                    struct aws_log_message *next0 = delete_list->next;
                    char *msg_data = (char*)(delete_list + 1);
                    global_log_report_callback(msg_data);
                    aws_memory_pool_release(&context->message_pool, delete_list);
                    delete_list = next0;
                }

                delete_list = log_list->delete_list;
                while (delete_list) {
                    struct aws_log_message *next0 = delete_list->next;
                    aws_memory_pool_release(&context->message_pool, delete_list);
                    delete_list = next0;
                }

                aws_memory_pool_clean_up(&log_list->message_pool);
            } else {
                aws_raise_error(AWS_ERROR_LOG_IMPROPER_CLEAN_UP);
                return AWS_OP_ERR;
            }

            log_list->alloc->mem_release(log_list->alloc, log_list);

            log_list = next;
        } while (log_list != sentinel);
    } else {
        aws_mutex_unlock(&global_log_list_mutex);
    }

    return AWS_OP_SUCCESS;
}
