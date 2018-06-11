#ifndef AWS_COMMON_LOGGER_H
#define AWS_COMMON_LOGGER_H
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
#include <aws/common/common.h>
#include <stdarg.h>

enum aws_log_level
{
    AWS_LOG_LEVEL_OFF = 0,
    AWS_LOG_LEVEL_FATAL = 1,
    AWS_LOG_LEVEL_ERROR = 2,
    AWS_LOG_LEVEL_WARN = 3,
    AWS_LOG_LEVEL_INFO = 4,
    AWS_LOG_LEVEL_DEBUG = 5,
    AWS_LOG_LEVEL_TRACE = 6
};

static inline const char *aws_get_log_level_name(enum aws_log_level level) {
    switch(level) {
        case AWS_LOG_LEVEL_OFF:
            return "OFF";
        case AWS_LOG_LEVEL_FATAL:
            return "FATAL";
        case AWS_LOG_LEVEL_ERROR:
            return "ERROR";
        case AWS_LOG_LEVEL_WARN:
            return "WARN";
        case AWS_LOG_LEVEL_INFO:
            return "INFO";
        case AWS_LOG_LEVEL_DEBUG:
            return "DEBUG";
        case AWS_LOG_LEVEL_TRACE:
            return "TRACE";
        default:
            return "UNKNOWN";
    }
}

static inline void aws_log(enum aws_log_level level, struct aws_allocator *alloc, const char *tag, const char *msg,
        va_list args) {

    /* TODO: implement this */
    char buf[256]; /* most log messages will fit here, for the larger ones, we'll need to dynamically allocate */
    (void)buf;
}

static inline void aws_log_fatal(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_FATAL, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_error(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_ERROR, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_warn(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_WARN, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_info(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_INFO, alloc, tag, msg, args);
    va_end(args);

}

static inline void aws_log_debug(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_DEBUG, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_trace(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(AWS_LOG_LEVEL_TRACE, alloc, tag, msg, args);
    va_end(args);
}

#endif /* AWS_COMMON_LOGGER_H */

