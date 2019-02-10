/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include "test_logger.h"

#include <aws/common/byte_buf.h>

#include <stdarg.h>
#include <stdio.h>

/**
 * A real logger wouldn't have such size restrictions, but these are good enough for our tests
 */
#define TEST_LOGGER_MAX_LOG_LINE_SIZE 256

int s_test_logger_log_fn(struct aws_logger *logger, enum aws_log_level log_level, aws_log_subject_t subject, const char *format, ...) {
    va_list format_args;
    va_start(format_args, format);

    static char buffer[TEST_LOGGER_MAX_LOG_LINE_SIZE];

#ifdef WIN32
    int written = vsnprintf_s(buffer, TEST_LOGGER_MAX_LOG_LINE_SIZE, _TRUNCATE, format, format_args);
#else
    int written = vsnprintf(buffer, TEST_LOGGER_MAX_LOG_LINE_SIZE, format, format_args);
#endif // WIN32
    if (written < 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    struct test_logger_impl *impl = (struct test_logger_impl *)logger->p_impl;

    if (aws_byte_buf_write(&impl->log_buffer, (uint8_t *)buffer, written)) {
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    return AWS_OP_SUCCESS;
}

enum aws_log_level s_test_logger_get_log_level_fn(struct aws_logger *logger, aws_log_subject_t subject) {
    struct test_logger_impl *impl = (struct test_logger_impl *)logger->p_impl;

    return impl->level;
}

int s_test_logger_cleanup(struct aws_logger *logger) {
    struct test_logger_impl *impl = (struct test_logger_impl *)logger->p_impl;

    aws_byte_buf_clean_up(&impl->log_buffer);

    struct aws_allocator* allocator = logger->allocator;
    aws_mem_release(allocator, impl);

    return AWS_OP_SUCCESS;
}

static struct aws_logger_vtable s_test_logger_vtable = {
        .get_log_level_fn = s_test_logger_get_log_level_fn,
        .log_fn = s_test_logger_log_fn,
        .cleanup_fn = s_test_logger_cleanup
};

int test_logger_init(struct aws_logger *logger, struct aws_allocator *allocator, enum aws_log_level level) {

    struct test_logger_impl *impl = (struct test_logger_impl *)aws_mem_acquire(allocator, sizeof(struct test_logger_impl));
    if (impl == NULL) {
        return aws_raise_error(AWS_ERROR_OOM);
    }

    if (aws_byte_buf_init(&impl->log_buffer, allocator, TEST_LOGGER_MAX_BUFFER_SIZE)) {
        aws_mem_release(allocator, impl);
        return AWS_OP_ERR;
    }

    impl->level = level;

    logger->vtable = &s_test_logger_vtable;
    logger->allocator = allocator;
    logger->p_impl = impl;

    return AWS_OP_SUCCESS;
}

int test_logger_get_contents(struct aws_logger *logger, char* buffer, size_t max_length)
{
    struct test_logger_impl *impl = (struct test_logger_impl *)logger->p_impl;
    if (max_length == 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    size_t copy_length = max_length - 1;
    if (impl->log_buffer.len < copy_length) {
        copy_length = impl->log_buffer.len;
    }

    if (copy_length > 0) {
        memcpy(buffer, impl->log_buffer.buffer, copy_length);
    }

    buffer[copy_length] = 0;

    return AWS_OP_SUCCESS;
}


