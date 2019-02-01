#ifndef AWS_COMMON_LOGGING_H
#define AWS_COMMON_LOGGING_H

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

#include <aws/common/common.h>

#define AWS_LOG_LEVEL_NONE 0
#define AWS_LOG_LEVEL_FATAL 1
#define AWS_LOG_LEVEL_ERROR 2
#define AWS_LOG_LEVEL_WARN 3
#define AWS_LOG_LEVEL_INFO 4
#define AWS_LOG_LEVEL_DEBUG 5
#define AWS_LOG_LEVEL_TRACE 6

enum aws_log_level {
    AWS_LL_NONE = AWS_LOG_LEVEL_NONE,
    AWS_LL_FATAL = AWS_LOG_LEVEL_FATAL,
    AWS_LL_ERROR = AWS_LOG_LEVEL_ERROR,
    AWS_LL_WARN = AWS_LOG_LEVEL_WARN,
    AWS_LL_INFO = AWS_LOG_LEVEL_INFO,
    AWS_LL_DEBUG = AWS_LOG_LEVEL_DEBUG,
    AWS_LL_TRACE = AWS_LOG_LEVEL_TRACE,

    AWS_LL_COUNT
};

typedef uint64_t aws_log_subject_t;

#define AWS_LOG_SUBJECT_NONE ((aws_log_subject_t)0)

struct aws_logger;



struct aws_logger_vtable {
    int(*log_fn)(struct aws_logger *logger, enum aws_log_level log_level, aws_log_subject_t subject, const char *format, ...);
    enum aws_log_level(*get_log_level_fn)(struct aws_logger *logger, aws_log_subject_t subject);
};

struct aws_logger {
    struct aws_logger_vtable *vtable;
    void *p_impl;
};

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_logging_set(struct aws_logger *logger);

AWS_COMMON_API
struct aws_logger *aws_logging_get(void);

AWS_COMMON_API
int aws_logging_log_level_to_string(enum aws_log_level log_level, const char **level_string);

AWS_EXTERN_C_END

#define LOGF_RAW(log_level, subject, format, ...) \
{ \
    struct aws_logger *logger = aws_logging_get(); \
    if (logger != NULL && (logger->vtable->get_log_level_fn)(logger, subject) >= log_level && log_level > 0) { \
        (logger->vtable->log_fn)(logger, log_level, subject, format, __VA_ARGS__);\
    } \
}

#define LOGF(log_level, format, ...) LOGF_RAW(log_level, AWS_LOG_SUBJECT_NONE, format, __VA_ARGS__)

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_FATAL)
#   define LOGF_FATAL(format, ...) LOGF(AWS_LL_FATAL, format, __VA_ARGS__)
#else
#   define LOGF_FATAL(fmt, ...)
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_ERROR)
#   define LOGF_ERROR(format, ...) LOGF(AWS_LL_ERROR, format, __VA_ARGS__)
#else
#   define LOGF_ERROR(fmt, ...)
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_WARN)
#   define LOGF_WARN(format, ...) LOGF(AWS_LL_WARN, format, __VA_ARGS__)
#else
#   define LOGF_WARN(fmt, ...)
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_INFO)
#   define LOGF_INFO(format, ...) LOGF(AWS_LL_INFO, format, __VA_ARGS__)
#else
#   define LOGF_INFO(fmt, ...)
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_DEBUG)
#   define LOGF_DEBUG(format, ...) LOGF(AWS_LL_DEBUG, format, __VA_ARGS__)
#else
#   define LOGF_DEBUG(fmt, ...)
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_TRACE)
#   define LOGF_TRACE(format, ...) LOGF(AWS_LL_TRACE, format, __VA_ARGS__)
#else
#   define LOGF_TRACE(fmt, ...)
#endif


#endif //AWS_COMMON_LOGGING_H
