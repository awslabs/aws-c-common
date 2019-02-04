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

#include <aws/common/logging.h>

#include <aws/common/common.h>

static enum aws_log_level s_null_logger_get_log_level_fn(struct aws_logger *logger, aws_log_subject_t subject) {
    return AWS_LL_NONE;
}

static int s_null_logger_log_fn(struct aws_logger *logger, enum aws_log_level log_level, aws_log_subject_t subject, const char *format, ...) {
    return AWS_OP_SUCCESS;
}

static struct aws_logger_vtable s_null_vtable = {
        .get_log_level_fn = s_null_logger_get_log_level_fn,
        .log_fn = s_null_logger_log_fn
};

static struct aws_logger s_null_logger = {
        .vtable = &s_null_vtable,
        .p_impl = NULL
};

static struct aws_logger *s_root_logger_ptr = &s_null_logger;

void aws_logging_set(struct aws_logger *logger) {
    if (logger != NULL) {
        s_root_logger_ptr = logger;
    } else {
        s_root_logger_ptr = &s_null_logger;
    }
}

struct aws_logger *aws_logging_get(void) {
    return s_root_logger_ptr;
}

static const char* s_log_level_strings[AWS_LL_COUNT] = {
    "NONE",
    "FATAL",
    "ERROR",
    "WARN",
    "INFO",
    "DEBUG",
    "TRACE"
};

int aws_logging_log_level_to_string(enum aws_log_level log_level, const char **level_string) {
    if (log_level >= AWS_LL_COUNT) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    if (level_string != NULL) {
        *level_string = s_log_level_strings[log_level];
    }

    return AWS_OP_SUCCESS;
}
