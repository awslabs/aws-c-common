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

enum aws_log_level
{
    aws_off = 0,
    aws_fatal = 1,
    aws_error = 2,
    aws_warn = 3,
    aws_info = 4,
    aws_debug = 5,
    aws_trace = 6
};

static inline const char *aws_get_log_level_name(enum aws_log_level level) {
    switch(level) {
        case aws_off:
            return "OFF";
        case aws_fatal:
            return "FATAL";
        case aws_error:
            return "ERROR";
        case aws_warn:
            return "WARN";
        case aws_info:
            return "INFO";
        case aws_debug:
            return "DEBUG";
        case aws_trace:
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
    aws_log(aws_fatal, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_error(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(aws_error, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_warn(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(aws_warn, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_info(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(aws_info, alloc, tag, msg, args);
    va_end(args);

}

static inline void aws_log_debug(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(aws_debug, alloc, tag, msg, args);
    va_end(args);
}

static inline void aws_log_trace(struct aws_allocator *alloc, const char *tag, const char *msg, ...) {
    va_list args;
    va_start(args, msg);
    aws_log(aws_trace, alloc, tag, msg, args);
    va_end(args);
}

#endif /* AWS_COMMON_LOGGER_H */

