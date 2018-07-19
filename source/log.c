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

#ifndef _CRT_SECURE_NO_WARNINGS
	#define _CRT_SECURE_NO_WARNINGS
#endif

#ifndef _CRT_NONSTDC_NO_DEPRECATE
	#define _CRT_NONSTDC_NO_DEPRECATE
#endif

#include <stdio.h>
#include <time.h>

#include <aws/common/atomic.h>
#include <aws/common/common.h>
#include <aws/common/log.h>
#include <aws/common/memory_pool.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#define AWS_CIRCULAR_DOUBLY_LIST_INIT(sentinel) \
    do { \
        (sentinel)->next = (sentinel); \
        (sentinel)->prev = (sentinel); \
    } while (0)

#define AWS_CIRCULAR_DOUBLY_LIST_INSERT_BEFORE(before_me, element) \
    do { \
        (element)->prev = (before_me); \
        (element)->next = (before_me)->next; \
        (before_me)->next->prev = (element); \
        (before_me)->next = (element); \
    } while (0)

#define AWS_CIRCULAR_DOUBLY_LIST_REMOVE(element) \
    do { \
        (element)->prev->next = (element)->next; \
        (element)->next->prev = (element)->prev; \
    } while (0)

#define AWS_SINGLY_LIST_REVERSE(T, list) \
    do { \
        T* reverse_node__ = 0; \
        while (list) { \
            T* reverse_next__ = list->next; \
            list->next = reverse_node__; \
            reverse_node__ = list; \
            list = reverse_next__; \
        } \
        list = reverse_node__; \
    } while (0)

struct aws_log_message {
    struct aws_log_message *next;
};

struct aws_log_context {
    struct aws_log_message *message_list;
    struct aws_log_message *delete_list;
    size_t max_message_len;
    struct aws_memory_pool* message_pool;
    struct aws_allocator *alloc;
    struct aws_log_context *next;
    struct aws_log_context *prev;
};

static void s_aws_log_default_report_function(const char* log_message) {
    (void)log_message;
}

int s_log_thread_count;
aws_log_report_fn* s_log_report_callback = s_aws_log_default_report_function;
struct aws_mutex s_log_list_mutex = AWS_MUTEX_INIT;
struct aws_log_context *s_log_list;

AWS_THREAD_LOCAL struct aws_log_context *s_local_log_context;

void aws_log_set_reporting_callback(aws_log_report_fn* report_callback) {
    if (report_callback) {
        s_log_report_callback = report_callback;
    } else {
        s_log_report_callback = s_aws_log_default_report_function;
    }
}

int aws_vlog(enum aws_log_level level, const char *fmt, va_list va_args) {
    (void)level;

    if (!s_local_log_context) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    /* Atomically grab and release all messages on the `delete_list` whenever present. */
    struct aws_log_message* delete_list;
    do {
        delete_list = s_local_log_context->delete_list;
    } while (!aws_atomic_cas_ptr((void **)&s_local_log_context->delete_list, delete_list, NULL));

    while (delete_list) {
        struct aws_log_message *next = delete_list->next;
        aws_memory_pool_release(s_local_log_context->message_pool, delete_list);
        delete_list = next;
    }

    /* Acquire memory for the new message. */
    void *mem = aws_memory_pool_acquire(s_local_log_context->message_pool);
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    char *msg_data = (char*)(msg + 1);
    
    /* Format the message. */
    char date[256];
    time_t now = time(NULL);
    struct tm *t = localtime(&now);
    strftime(date, sizeof(date) - 1, "%d %m %Y %H:%M", t);

    char fmt_final[1024];
    snprintf(fmt_final, sizeof(fmt_final), "[%s] %s [%d] %s\n", aws_log_level_to_string(level), date, (unsigned)aws_thread_current_thread_id(), fmt);

    vsnprintf(msg_data, s_local_log_context->max_message_len, fmt_final, va_args);
    if (strlen(msg_data) == s_local_log_context->max_message_len - 1) {
        msg_data[s_local_log_context->max_message_len - 2] = '\n';
    }

    /* Push formatted message onto this thread's message list. Will be picked up later and
    processed by the logging thread in `aws_log_flush()`, and handed to a user callback set by
    `aws_log_set_reporting_callback`. */
    do {
        msg->next = s_local_log_context->message_list;
    } while (!aws_atomic_cas_ptr((void **)&s_local_log_context->message_list, msg->next, msg));

    return AWS_OP_SUCCESS;
}

int aws_log(enum aws_log_level level, const char *fmt, ...) {
    if (!s_local_log_context) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    va_list va_args;
    va_start(va_args, fmt);
    int ret = aws_vlog(level, fmt, va_args);
    va_end(va_args);
    return ret;
}

const char *aws_log_level_to_string(enum aws_log_level level) {
    switch (level) {
        case AWS_LOG_LEVEL_OFF:   return "OFF";
        case AWS_LOG_LEVEL_FATAL: return "FATAL";
        case AWS_LOG_LEVEL_ERROR: return "ERROR";
        case AWS_LOG_LEVEL_WARN:  return "WARN";
        case AWS_LOG_LEVEL_TRACE: return "TRACE";
        default: return NULL;
    }
}

int aws_log_flush() {
    struct aws_log_context *log_list = s_log_list;
    struct aws_log_context *sentinel = log_list;
    do {
        struct aws_log_context *next = log_list->next;

        /* Grab the message list, atomically. */
        struct aws_log_message* msg_list;
        do {
            msg_list = log_list->message_list;
        } while (!aws_atomic_cas_ptr((void **)&log_list->message_list, msg_list, NULL));

        /* Reverse the list to preserve user submitted order, for reporting. */
        if (msg_list) {
            struct aws_log_message *last_msg = msg_list;
            AWS_SINGLY_LIST_REVERSE(struct aws_log_message, msg_list);
            /* AWS_ASSERT(last_msg->next == NULL); */

            /* Report logs to the user. */
            struct aws_log_message *msg = msg_list;
            while (msg) {
                char *msg_data = (char*)(msg + 1);
                s_log_report_callback(msg_data);
                msg = msg->next;
            }

            /* Release all messages to the thread local memory pool by appending to the `delete_list`. */
            do {
                last_msg->next = log_list->delete_list;
            } while (!aws_atomic_cas_ptr((void **)&log_list->delete_list, last_msg->next, msg_list));
        }

        log_list = next;
    } while (log_list != sentinel);

    return AWS_OP_SUCCESS;
}

int aws_log_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count) {
    if (aws_atomic_get_ptr((void **)&s_local_log_context)) {
        aws_raise_error(AWS_ERROR_LOG_DOUBLE_INITIALIZE);
        return AWS_OP_ERR;
    }

    if (max_message_len < 1) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    aws_atomic_add(&s_log_thread_count, 1);
    aws_atomic_set_ptr((void **)&s_local_log_context, aws_mem_acquire(alloc, sizeof(struct aws_log_context)));
    if (!s_local_log_context) {
        aws_raise_error(AWS_ERROR_OOM);
        return AWS_OP_ERR;
    }

    aws_secure_zero(s_local_log_context, sizeof(*s_local_log_context));
    s_local_log_context->max_message_len = max_message_len;
    s_local_log_context->alloc = alloc;
    s_local_log_context->message_pool = aws_memory_pool_init(alloc, sizeof(struct aws_log_message) + max_message_len, memory_pool_message_count);
    if (!s_local_log_context->message_pool) {
        aws_raise_error(AWS_ERROR_OOM);
        return AWS_OP_ERR;
    }
    AWS_CIRCULAR_DOUBLY_LIST_INIT(s_local_log_context);

    /* Insert thread local log info struct onto the global doubly linked list used by
    the logging thread. */
    aws_mutex_lock(&s_log_list_mutex);
    if (!s_log_list) {
        s_log_list = s_local_log_context;
    } else {
        AWS_CIRCULAR_DOUBLY_LIST_INSERT_BEFORE(s_log_list, s_local_log_context);
    }
    aws_mutex_unlock(&s_log_list_mutex);


    return AWS_OP_SUCCESS;
}

int aws_log_clean_up() {
    if (aws_atomic_get(&s_log_thread_count) == 0) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    struct aws_log_context *context;
    do {
        context = s_local_log_context;
    } while (!aws_atomic_cas_ptr((void **)&s_local_log_context, context, NULL));

    /* Perform final cleanup if this is the last log thread. */
    aws_mutex_lock(&s_log_list_mutex);
    if (aws_atomic_add(&s_log_thread_count, -1) == 1) {
        struct aws_log_context *log_list = s_log_list;
        s_log_list = NULL;
        aws_mutex_unlock(&s_log_list_mutex);

        /* Make sure all the other log threads have been joined and remove dead threads. */
        struct aws_log_context *sentinel = log_list;
        do {
            struct aws_log_context *next = log_list->next;

            /* Remove dead threads. Log any leftover messages. Cleanup leftover message pool memory. */
            struct aws_log_message *delete_list = log_list->message_list;
            while (delete_list) {
                struct aws_log_message *next0 = delete_list->next;
                char *msg_data = (char*)(delete_list + 1);
                s_log_report_callback(msg_data);
                aws_memory_pool_release(log_list->message_pool, delete_list);
                delete_list = next0;
            }

            delete_list = log_list->delete_list;
            while (delete_list) {
                struct aws_log_message *next0 = delete_list->next;
                aws_memory_pool_release(log_list->message_pool, delete_list);
                delete_list = next0;
            }

            aws_memory_pool_clean_up(log_list->message_pool);
            aws_mem_release(log_list->alloc, log_list);

            log_list = next;
        } while (log_list != sentinel);
    } else {
        aws_mutex_unlock(&s_log_list_mutex);
    }

    return AWS_OP_SUCCESS;
}
