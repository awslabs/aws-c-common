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

/**
 * Controls what log calls pass through the logger and what log calls get filtered out.
 * If a log level has a value of X, then all log calls using a level <= X will appear, while
 * those using a value > X will not occur.
 *
 * You can filter both dynamically (by setting the log level on the logger object) or statically
 * (by defining AWS_STATIC_LOG_LEVEL to be an appropriate integer module-wide).  Statically filtered
 * log calls will be completely compiled out but require a rebuild if you want to get more detail
 * about what's happening.
 */
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

/**
 * Log subject is a to-be-defined key, indendent of level, that will allow for additional filtering options.
 *
 * The general idea is to support the logging of related functionality and allow for level control with a
 * finer-grained approach.
 *
 * For example, enable TRACE logging for mqtt-related log statements, but only WARN logging everywhere else.
 */
typedef uint64_t aws_log_subject_t;

#define AWS_LOG_SUBJECT_NONE ((aws_log_subject_t)0)

struct aws_logger;

/**
 * We separate the log level function from the log call itself so that we can do the filter check in the macros (see below)
 *
 * By doing so, we make it so that the variadic format arguments are not even evaluated if the filter check does not succeed.
 */
struct aws_logger_vtable {
    int(*log_fn)(struct aws_logger *logger, enum aws_log_level log_level, aws_log_subject_t subject, const char *format, ...);
    enum aws_log_level(*get_log_level_fn)(struct aws_logger *logger, aws_log_subject_t subject);
    int(*cleanup_fn)(struct aws_logger *logger);
};

struct aws_logger {
    struct aws_logger_vtable *vtable;
    struct aws_allocator *allocator;
    void *p_impl;
};

AWS_EXTERN_C_BEGIN

/**
 * Sets the aws logger used globally across the process.  Not thread-safe.  Must only be called once.
 */
AWS_COMMON_API
void aws_logging_set(struct aws_logger *logger);

/**
 * Gets the aws logger used globally across the process.
 */
AWS_COMMON_API
struct aws_logger *aws_logging_get(void);

/**
 * Cleans up all resources used by the logger; simply invokes the cleanup v-function
 */
AWS_COMMON_API
int aws_logger_cleanup(struct aws_logger *logger);

/**
 * Converts a log level to a c-string constant.  Intended primarily to support building log lines that
 * include the level in them, i.e.
 *
 * [ERROR] 10:34:54.642 01-31-19 - Json parse error....
 */
AWS_COMMON_API
int aws_logging_log_level_to_string(enum aws_log_level log_level, const char **level_string);

AWS_EXTERN_C_END

/**
 * The base formatted logging macro that all other formatted logging macros resolve to.
 * Checks for a logger and filters based on log level.
 */
#define LOGF_RAW(log_level, subject, format, ...)                                                               \
(((aws_logging_get()->vtable->get_log_level_fn)(aws_logging_get(), subject) >= log_level && log_level > 0) ?    \
(aws_logging_get()->vtable->log_fn)(aws_logging_get(), log_level, subject, format, __VA_ARGS__) :               \
AWS_OP_SUCCESS)

#define LOGF(log_level, format, ...) LOGF_RAW(log_level, AWS_LOG_SUBJECT_NONE, format, __VA_ARGS__)

/**
 * LOGF_<level> variants for each level.  These are what should be used directly to do all logging.
 *
 * i.e.
 *
 * LOGF_FATAL("Device \"%s\" not found", device->name);
 *
 * or
 *
 * if (LOGF_FATAL("Device \"%s\" not found", device->name)) {
 *     ... handle logging error
 * }
 *
 * Later we will likely expose Subject-aware variants
 */
#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_FATAL)
#   define LOGF_FATAL(format, ...) LOGF(AWS_LL_FATAL, format, __VA_ARGS__)
#else
#   define LOGF_FATAL(format, ...) AWS_OP_SUCCESS
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_ERROR)
#   define LOGF_ERROR(format, ...) LOGF(AWS_LL_ERROR, format, __VA_ARGS__)
#else
#   define LOGF_ERROR(format, ...) AWS_OP_SUCCESS
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_WARN)
#   define LOGF_WARN(format, ...) LOGF(AWS_LL_WARN, format, __VA_ARGS__)
#else
#   define LOGF_WARN(format, ...) AWS_OP_SUCCESS
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_INFO)
#   define LOGF_INFO(format, ...) LOGF(AWS_LL_INFO, format, __VA_ARGS__)
#else
#   define LOGF_INFO(format, ...) AWS_OP_SUCCESS
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_DEBUG)
#   define LOGF_DEBUG(format, ...) LOGF(AWS_LL_DEBUG, format, __VA_ARGS__)
#else
#   define LOGF_DEBUG(format, ...) AWS_OP_SUCCESS
#endif

#if !defined(AWS_STATIC_LOG_LEVEL) || (AWS_STATIC_LOG_LEVEL >= AWS_LOG_LEVEL_TRACE)
#   define LOGF_TRACE(format, ...) LOGF(AWS_LL_TRACE, format, __VA_ARGS__)
#else
#   define LOGF_TRACE(format, ...) AWS_OP_SUCCESS
#endif


#endif /* AWS_COMMON_LOGGING_H */
