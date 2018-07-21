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

#include <aws/common/log.h>

#include <aws/common/atomic.h>
#include <aws/common/common.h>
#include <aws/common/memory_pool.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>


#include <stdio.h>
#include <time.h>
#include <inttypes.h>

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

#define AWS_ATOMIC_SINGLY_LIST_INSERT(head, node) \
    do { \
        do { \
            (node)->next = (head); \
        } while (!aws_atomic_cas_ptr((void **)&(head), (node)->next, (node))); \
    } while (0)

struct aws_log_message {
    struct aws_log_message *next;
};

struct aws_log_context {
    struct aws_log_message *message_list;
    struct aws_log_message *delete_list;
    size_t max_message_len;
    int table_index;
    struct aws_memory_pool* message_pool;
    struct aws_allocator *alloc;
};

enum aws_log_entry_state {
    AWS_LOG_ENTRY_STATE_NO_WRITERS,
    AWS_LOG_ENTRY_STATE_WRITER,
    AWS_LOG_ENTRY_STATE_DELETEME,
};

struct aws_log_context_entry {
    int state;
    struct aws_log_context *ctx;
};

struct aws_log_system_params {
    size_t max_message_len;
    int memory_pool_message_count;
    int max_message_count;
    struct aws_allocator *alloc;
};

static void s_aws_log_default_report_function(const char *log_message) {
    (void)log_message;
}

static int s_log_message_count;
static int s_log_system_running;
static struct aws_log_system_params s_log_system_params;

static int s_log_context_count;
static struct aws_log_context_entry s_log_table[AWS_LOG_MAX_LOGGING_THREADS];
static aws_log_report_fn* s_log_report_callback = s_aws_log_default_report_function;

AWS_THREAD_LOCAL struct aws_log_context *s_local_log_context;

void aws_log_set_reporting_callback(aws_log_report_fn* report_callback) {
    if (report_callback) {
        s_log_report_callback = report_callback;
    } else {
        s_log_report_callback = s_aws_log_default_report_function;
    }
}

int aws_log_system_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count, int max_message_count) {
    if (max_message_len < 1 || max_message_count < 1) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return AWS_OP_ERR;
    }

    if (!aws_atomic_cas(&s_log_system_running, 0, 1)) {
        aws_raise_error(AWS_ERROR_LOG_DOUBLE_INITIALIZE);
        return AWS_OP_ERR;
    }

    s_log_system_params.max_message_len = max_message_len;
    s_log_system_params.memory_pool_message_count = memory_pool_message_count;
    s_log_system_params.max_message_count = max_message_count;
    s_log_system_params.alloc = alloc;

    aws_log_thread_init();

    return AWS_OP_SUCCESS;
}

void aws_log_system_clean_up() {
    s_log_system_running = 0;
    aws_log_thread_clean_up();
    aws_log_flush();
}

int aws_vlog(enum aws_log_level level, const char *fmt, va_list va_args) {
    if (!s_local_log_context) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    if (aws_atomic_add(&s_log_message_count, 1) >= s_log_system_params.max_message_count) {
        aws_raise_error(AWS_ERROR_LOG_THREAD_MAX_CAPACITY);
        aws_atomic_add(&s_log_message_count, -1);
        return AWS_OP_ERR;
    }

    /* Atomically grab and release all messages on the `delete_list` whenever present. */
    struct aws_log_message *delete_list;
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
    if (!mem) {
        return AWS_OP_ERR;
    }
    struct aws_log_message *msg = (struct aws_log_message *)mem;
    char *msg_data = (char*)(msg + 1);
    
    /* Format the message. */
    char date[256];
    time_t now = time(NULL);
    /* TODO: localtime isn't thread safe, call localtime_r on posix systems and localtime is fine on windows. */
    struct tm *t = localtime(&now);
    strftime(date, sizeof(date) - 1, "%m-%d-%Y %H:%M:%S:%Z", t);

    char fmt_final[1024];
    snprintf(fmt_final, sizeof(fmt_final), "[%s] %s [%" PRIu64 "] %s\n", aws_log_level_to_string(level), date,
             aws_thread_current_thread_id(), fmt);

    vsnprintf(msg_data, s_local_log_context->max_message_len, fmt_final, va_args);
    if (strlen(msg_data) == s_local_log_context->max_message_len - 1) {
        msg_data[s_local_log_context->max_message_len - 2] = '\n';
    }

    /* Push formatted message onto this thread's message list. Will be picked up later and
    processed by the logging thread in `aws_log_flush()`, and handed to a user callback set by
    `aws_log_set_reporting_callback`. */
    AWS_ATOMIC_SINGLY_LIST_INSERT(s_local_log_context->message_list, msg);

    return AWS_OP_SUCCESS;
}

int aws_log(enum aws_log_level level, const char *fmt, ...) {
    if (!s_local_log_context || !s_log_system_running) {
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

static void s_aws_log_remove_dead_context(int index) {
    assert(index >= 0 && index < AWS_LOG_MAX_LOGGING_THREADS);

    /* Atomically grab the ctx pointer for this index. */
    struct aws_log_context* ctx = aws_atomic_set_ptr((void **)&s_log_table[index].ctx, NULL);

    if (ctx) {
        /* Cleanup all resources for this context. */
        struct aws_log_message *msg_list = ctx->message_list;
        AWS_SINGLY_LIST_REVERSE(struct aws_log_message, msg_list);
        int count = 0;

        while (msg_list) {
            struct aws_log_message *next0 = msg_list->next;
            char *msg_data = (char*)(msg_list + 1);
            s_log_report_callback(msg_data);
            aws_memory_pool_release(ctx->message_pool, msg_list);
            msg_list = next0;
            ++count;
        }

        aws_atomic_add(&s_log_message_count, -count);

        struct aws_log_message *delete_list = ctx->delete_list;
        while (delete_list) {
            struct aws_log_message *next0 = delete_list->next;
            aws_memory_pool_release(ctx->message_pool, delete_list);
            delete_list = next0;
        }

        aws_memory_pool_clean_up(ctx->message_pool);
        aws_mem_release(ctx->alloc, ctx);
    }

    if (aws_atomic_cas(&s_log_table[index].state, AWS_LOG_ENTRY_STATE_DELETEME, AWS_LOG_ENTRY_STATE_NO_WRITERS)) {
        aws_atomic_add(&s_log_context_count, -1);
    }
}

int aws_log_flush() {
    for (int i = 0; i < AWS_LOG_MAX_LOGGING_THREADS; ++i) {
        int state = aws_atomic_set(&s_log_table[i].state, AWS_LOG_ENTRY_STATE_WRITER);
        if (state != AWS_LOG_ENTRY_STATE_NO_WRITERS) {
            if (state == AWS_LOG_ENTRY_STATE_DELETEME) {
                s_aws_log_remove_dead_context(i);
            }
            continue;
        }

        /* Skip empty indices. */
        struct aws_log_context *ctx = s_log_table[i].ctx;
        if (!ctx) {
            s_log_table[i].state = AWS_LOG_ENTRY_STATE_NO_WRITERS;
            continue;
        }

        struct aws_log_message *msg_list = aws_atomic_set_ptr((void **)&ctx->message_list, NULL);

        /* Reverse the list to preserve user submitted order, for reporting. */
        if (msg_list) {
            struct aws_log_message *last_msg = msg_list;
            AWS_SINGLY_LIST_REVERSE(struct aws_log_message, msg_list);
            assert(last_msg->next == NULL);

            /* Report logs to the user. */
            struct aws_log_message *msg = msg_list;
            int count = 0;
            while (msg) {
                char *msg_data = (char*)(msg + 1);
                s_log_report_callback(msg_data);
                msg = msg->next;
                ++count;
            }

            aws_atomic_add(&s_log_message_count, -count);

            /* Release all messages to the thread local memory pool by appending to the `delete_list`. */
            do {
                last_msg->next = ctx->delete_list;
            } while (!aws_atomic_cas_ptr((void **)&ctx->delete_list, last_msg->next, msg_list));
        }

        if (!aws_atomic_cas(&s_log_table[i].state, AWS_LOG_ENTRY_STATE_WRITER, AWS_LOG_ENTRY_STATE_NO_WRITERS)) {
            /* The state was AWS_LOG_ENTRY_STATE_DELETEME. */
            s_aws_log_remove_dead_context(i);
        }
    }

    return AWS_OP_SUCCESS;
}

int aws_log_thread_init() {
    if (!s_log_system_running) {
        aws_raise_error(AWS_ERROR_LOG_UNINITIALIZED);
        return AWS_OP_ERR;
    }

    if (s_local_log_context) {
        aws_raise_error(AWS_ERROR_LOG_DOUBLE_INITIALIZE);
        return AWS_OP_ERR;
    }

    s_local_log_context = (struct aws_log_context *)aws_mem_acquire(s_log_system_params.alloc, sizeof(struct aws_log_context));
    if (!s_local_log_context) {
        return AWS_OP_ERR;
    }

    aws_secure_zero(s_local_log_context, sizeof(*s_local_log_context));
    s_local_log_context->max_message_len = s_log_system_params.max_message_len;
    s_local_log_context->alloc = s_log_system_params.alloc;
    s_local_log_context->message_pool = aws_memory_pool_init(s_log_system_params.alloc, sizeof(struct aws_log_message) + s_log_system_params.max_message_len, s_log_system_params.memory_pool_message_count);
    if (!s_local_log_context->message_pool) {
        aws_mem_release(s_log_system_params.alloc, s_local_log_context);
        s_local_log_context = NULL;
        return AWS_OP_ERR;
    }

    /* Insert this thread log context into the global table. */
    int space_available = aws_atomic_add(&s_log_context_count, 1) < AWS_LOG_MAX_LOGGING_THREADS;
    if (space_available) {
        /* Loop here to account for contention on cas (can happen if many threads call `aws_log_flush` and starve out this table insertion. */
        while (1) {
            int found_space = 0;
            for (int i = 0; i < AWS_LOG_MAX_LOGGING_THREADS; ++i) {
                if (aws_atomic_cas(&s_log_table[i].state, AWS_LOG_ENTRY_STATE_NO_WRITERS, AWS_LOG_ENTRY_STATE_WRITER)) {
                    if (!s_log_table[i].ctx) {
                        s_log_table[i].ctx = s_local_log_context;
                        s_local_log_context->table_index = i;
                        s_log_table[i].state = AWS_LOG_ENTRY_STATE_NO_WRITERS;
                        found_space = 1;
                    }

                    if (found_space) {
                        return AWS_OP_SUCCESS;
                    }
                }
            }
        }
    } else {
        aws_atomic_add(&s_log_context_count, -1);
        aws_mem_release(s_log_system_params.alloc, s_local_log_context);
        s_local_log_context = NULL;
        aws_raise_error(AWS_ERROR_LOG_THREAD_MAX_CAPACITY);
        return AWS_OP_ERR;
    }
}

int aws_log_thread_clean_up() {
    if (aws_atomic_get(&s_log_context_count) == 0 || s_local_log_context == NULL) {
        return AWS_OP_ERR;
    }

    int index = s_local_log_context->table_index;
    s_local_log_context = NULL;
    aws_atomic_set(&s_log_table[index].state, AWS_LOG_ENTRY_STATE_DELETEME);

    return AWS_OP_SUCCESS;
}
