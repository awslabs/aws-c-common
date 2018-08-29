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

#include <aws/common/mutex.h>
#include <aws/common/log.h>

struct s_ctx {
    struct aws_allocator *alloc;
    void *msg_pool;
    struct aws_mutex mutex;
};

struct s_ctx *s_ctx;
aws_log_report_fn *s_report;
enum aws_log_level s_level;

void aws_log_set_reporting_callback(aws_log_report_fn *report_callback) {
    s_report = report_callback;
}

int aws_log_system_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count, int max_message_count, enum aws_log_level level) {
    s_ctx = (struct s_ctx *)aws_mem_acquire(alloc, sizeof(*s_ctx));
    s_ctx->alloc = alloc;
    s_ctx->msg_pool = NULL;
    aws_mutex_init(&s_ctx->mutex);
}

void aws_log_system_set_level(enum aws_log_level level) {
    s_level = level;
}

enum aws_log_level aws_log_system_get_level(void) {
    return s_level;
}

void aws_log_system_clean_up() {
    aws_mutex_clean_up(&s_ctx->mutex);
    aws_mem_release(s_ctx->alloc, s_ctx);
}

int aws_log(enum aws_log_level level, const char *fmt, ...) {
}

int aws_vlog(enum aws_log_level level, const char *fmt, va_list va_args) {
}

const char *aws_log_level_to_string(enum aws_log_level level) {
}

int aws_log_flush() {
}

int aws_log_spawn_log_thread() {
}
