#ifndef AWS_COMMON_LOG_H
#define AWS_COMMON_LOG_H

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

#include <stdarg.h>

#include <aws/common/memory_pool.h>
#include <aws/common/linked_list.h>

enum aws_log_level
{
    AWS_LOG_LEVEL_OFF = 0, /* No logs will be processed at all. */
    AWS_LOG_LEVEL_FATAL,
    AWS_LOG_LEVEL_ERROR,
    AWS_LOG_LEVEL_WARN,
    AWS_LOG_LEVEL_INFO,
    AWS_LOG_LEVEL_DEBUG,
    AWS_LOG_LEVEL_TRACE
};

#define AWS_DEFAULT_LOG_LEVEL AWS_LOG_LEVEL_TRACE

#ifndef AWS_LOG_LEVEL
#define AWS_LOG_LEVEL AWS_DEFAULT_LOG_LEVEL
#endif /* AWS_LOG_LEVEL */

#define AWS_LOG(level, fmt, ...) \
    do { \
        AWS_WARNING_PUSH \
        AWS_WARNING_DISABLE_CONST_CONDITIONAL \
        if ((level) <= AWS_LOG_LEVEL) { \
            aws_log((level), (fmt), ## __VA_ARGS__); \
        } \
        AWS_WARNING_POP \
    } while (0)

#define AWS_VLOG(level, fmt, va_args) \
    do { \
        AWS_WARNING_PUSH \
        AWS_WARNING_DISABLE_CONST_CONDITIONAL \
        if ((level) <= AWS_LOG_LEVEL) { \
            aws_vlog((level), (fmt), (va_args)); \
        } \
        AWS_WARNING_POP \
    } while (0)

typedef void (aws_log_report_fn)(const char* log_message);

#define AWS_LOG_MAX_LOGGING_THREADS (256)

#ifdef __cplusplus
extern "C" {
#endif

/**
 * `report_callback` is called from inside of `aws_log_flush`. Each message logged will be reported to this callback.
 * The default reporting mechanism is an empty stub function (no-op).
 */
AWS_COMMON_API void aws_log_set_reporting_callback(aws_log_report_fn* report_callback);

/**
 * Initializes the logging system to capture future calls to `aws_log` and `aws_vlog`. The settings here are shared amongst
 * all other instances of `aws_thread` when `aws_thread_launch` is called.
 */
AWS_COMMON_API int aws_log_system_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count, int max_message_count);

/**
 * Cleans up all logging related resources and flushes any remaining logs.
 */
AWS_COMMON_API void aws_log_system_clean_up();

/**
 * Records a log entry to be processed by a later call to `aws_log_flush`.
 */
AWS_COMMON_API int aws_log(enum aws_log_level level, const char *fmt, ...);

/**
 * Records a log entry to be processed by a later call to `aws_log_flush`.
 */
AWS_COMMON_API int aws_vlog(enum aws_log_level level, const char *fmt, va_list va_args);

/**
 * Returns the string representation of `level` as an `aws_log_level` enum type.
 */
AWS_COMMON_API const char *aws_log_level_to_string(enum aws_log_level level);

/**
 * Call this function to process any previous logs captured by `aws_log` calls. Can be called in a loop, on a condition variable,
 * or by any other means deemed necessary. See `aws_log_default_process_thread_spawn` and `aws_log_default_process_thread_clean_up`.
 * Will periodically call `report_callback` from \ref aws_log_set_reporting_callback.
 */
AWS_COMMON_API int aws_log_flush();

/**
 * Initializes the calling thread so subsequent calls to `aws_log` are properly captured. `aws_thread` has this functionality
 * baked into them, and do not need to manually call init/clean_up.
 */
AWS_COMMON_API int aws_log_thread_init();

/**
 * Cleans up all resources allocated by the calling thread's previous call to `aws_log_thread_init`. The final thread to call this function
 * will clean up all resources and will *not* flush any remaining messages.
 */
AWS_COMMON_API int aws_log_thread_clean_up();

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_LOG_H */
