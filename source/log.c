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

#include <aws/common/condition_variable.h>
#include <aws/common/linked_list.h>
#include <aws/common/log.h>
//#include <aws/common/memory_pool.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#include <inttypes.h>
#include <stdio.h>
#include <time.h>

struct s_msg {
    struct aws_linked_list_node node;
    const char *tag;
};

struct s_ctx {
    struct aws_allocator *alloc;
    void *msg_pool;
    struct aws_mutex mutex;
    size_t message_size;
    struct aws_linked_list messages;
};

/* Logging globals. */
struct s_ctx *s_ctx;
aws_log_report_fn *s_report;
enum aws_log_level s_level;

/* Logging thread state. */
bool s_log_thread_running;
struct aws_thread s_log_thread;
struct aws_condition_variable s_cv = AWS_CONDITION_VARIABLE_INIT;
struct aws_mutex s_cv_mutex = AWS_MUTEX_INIT;
bool s_cv_state;

static inline struct s_msg *s_msg_new(void) {
    if (!s_ctx) {
        return NULL;
    }

    aws_mutex_lock(&s_ctx->mutex);
    struct s_msg *msg = (struct s_msg *)aws_mem_acquire(s_ctx->alloc, s_ctx->message_size);
    aws_mutex_unlock(&s_ctx->mutex);

    return msg;
}

static inline void s_msg_destroy(struct s_msg *msg) {
    if (s_ctx) {
        aws_mutex_lock(&s_ctx->mutex);
        aws_mem_release(s_ctx->alloc, msg);
        aws_mutex_unlock(&s_ctx->mutex);
    }
}

static inline char *s_get_msg_data(struct s_msg *msg) {
    return (char *)(msg + 1);
}

void aws_log_set_reporting_callback(aws_log_report_fn *report_callback) {
    s_report = report_callback;
}

int aws_log_system_init(
    struct aws_allocator *alloc,
    size_t max_message_len,
    int memory_pool_message_count,
    enum aws_log_level level) {
    s_ctx = (struct s_ctx *)aws_mem_acquire(alloc, sizeof(*s_ctx));
    s_ctx->alloc = alloc;
    s_ctx->msg_pool = NULL;
    s_ctx->message_size = max_message_len;
    (void)memory_pool_message_count;
    aws_mutex_init(&s_ctx->mutex);
    aws_linked_list_init(&s_ctx->messages);
    aws_log_system_set_level(level);
}

void aws_log_system_set_level(enum aws_log_level level) {
    s_level = level;
}

enum aws_log_level aws_log_system_get_level(void) {
    return s_level;
}

void aws_log_system_clean_up() {
    // TODO: Delete all messages.
    aws_mutex_clean_up(&s_ctx->mutex);
    // TODO: Clean up log thread.
    struct s_ctx *ctx = s_ctx;
    s_ctx = NULL;
    aws_mem_release(ctx->alloc, ctx);
}

int aws_log(enum aws_log_level level, const char *tag, const char *fmt, ...) {
    if (!(level != AWS_LOG_LEVEL_OFF && level >= s_level)) {
        return AWS_OP_SUCCESS;
    }

    if (!s_ctx) {
        return aws_raise_error(AWS_ERROR_LOG_FAILURE);
    }

    va_list va_args;
    va_start(va_args, fmt);
    int ret = aws_vlog(level, tag, fmt, va_args);
    va_end(va_args);
    return ret;
}

int aws_vlog(enum aws_log_level level, const char *tag, const char *fmt, va_list va_args) {
    if (!(level != AWS_LOG_LEVEL_OFF && level >= s_level)) {
        return AWS_OP_SUCCESS;
    }

    if (!s_ctx) {
        return aws_raise_error(AWS_ERROR_LOG_FAILURE);
    }

    /* Make new message. */
    struct s_msg *msg = s_msg_new();
    msg->tag = tag;
    char *msg_data = s_get_msg_data(msg);

    /* Format message. */
    char date[256];
    time_t now = time(NULL);
#ifdef _MSC_VER
    struct tm *t = localtime(&now);
    strftime(date, sizeof(date) - 1, "%m-%d-%Y %H:%M:%S:%Z", t);
#else
    struct tm t;
    localtime_r(&now, &t);
    strftime(date, sizeof(date) - 1, "%m-%d-%Y %H:%M:%S:%Z", &t);
#endif

    char fmt_final[1024];
    snprintf(
        fmt_final,
        sizeof(fmt_final),
        "[%s] %s [%" PRIu64 "] %s\n",
        aws_log_level_to_string(level),
        date,
        aws_thread_current_thread_id(),
        fmt);

    int count = vsnprintf(msg_data, s_ctx->message_size, fmt_final, va_args);
    if ((size_t)count >= s_ctx->message_size - 1) {
        msg_data[s_ctx->message_size - 2] = '\n';
    }

    /* Push message onto queue. */
    aws_mutex_lock(&s_ctx->mutex);
    aws_linked_list_push_front(&s_ctx->messages, msg);
    aws_mutex_unlock(&s_ctx->mutex);

    if (s_log_thread_running) {
        /* Notify log thread. */
        s_cv_state = true;
        aws_condition_variable_notify_one(&s_cv);
    }

    return AWS_OP_SUCCESS;
}

const char *aws_log_level_to_string(enum aws_log_level level) {
    switch (level) {
        case AWS_LOG_LEVEL_OFF:
            return "OFF";
        case AWS_LOG_LEVEL_FATAL:
            return "FATAL";
        case AWS_LOG_LEVEL_ERROR:
            return "ERROR";
        case AWS_LOG_LEVEL_WARN:
            return "WARN";
        case AWS_LOG_LEVEL_TRACE:
            return "TRACE";
        default:
            return NULL;
    }
}

int aws_log_flush() {
    if (!s_ctx) {
        return aws_raise_error(AWS_ERROR_LOG_FAILURE);
    }

    while (1) {
        /* Pop message off of queue. */
        aws_mutex_lock(&s_ctx->mutex);
        if (aws_linked_list_empty(&s_ctx->messages)) {
            aws_mutex_unlock(&s_ctx->mutex);
            break;
        }
        struct s_msg *msg = aws_linked_list_pop_back(&s_ctx->messages);
        aws_mutex_unlock(&s_ctx->mutex);

        /* Report message. */
        char *msg_data = s_get_msg_data(msg);
        if (s_report) {
            s_report(msg->tag, msg_data);
        }

        /* Clean up message. */
        s_msg_destroy(msg);
    }

    return AWS_OP_SUCCESS;
}

void s_log_thread_function(void *arg) {
    (void)arg;

    while (s_log_thread_running) {
        if (aws_log_flush() != AWS_OP_SUCCESS) {
            aws_log_destroy_log_thread();
            break;
        }

        while (!s_cv_state) {
            aws_condition_variable_wait(&s_cv, &s_cv_mutex);
        }
    }
}

int aws_log_spawn_log_thread(struct aws_allocator *alloc) {
    int ret = aws_thread_init(&s_log_thread, alloc);
    if (ret != AWS_OP_SUCCESS) {
        return ret;
    }

    ret = aws_thread_launch(&s_log_thread, s_log_thread_function, NULL, NULL);

    return ret;
}

void aws_log_destroy_log_thread() {
    s_log_thread_running = false;
    s_cv_state = true;
    aws_condition_variable_notify_one(&s_cv);
}
