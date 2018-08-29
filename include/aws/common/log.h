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

#include <aws/common/exports.h>
//#include <aws/common/memory_pool.h>

#include <stdarg.h>

enum aws_log_level {
    AWS_LOG_LEVEL_OFF = 0, /* No logs will be processed at all. */
    AWS_LOG_LEVEL_FATAL,
    AWS_LOG_LEVEL_ERROR,
    AWS_LOG_LEVEL_WARN,
    AWS_LOG_LEVEL_INFO,
    AWS_LOG_LEVEL_DEBUG,
    AWS_LOG_LEVEL_TRACE
};

typedef void (aws_log_report_fn)(const char *log_message);

#ifdef __cplusplus
extern "C" {
#endif

/**
 * `report_callback` is called from inside of `aws_log_flush`. Each message logged will be reported to this callback.
 * The default reporting mechanism is an empty stub function (no-op).
 */
AWS_COMMON_API void aws_log_set_reporting_callback(aws_log_report_fn *report_callback);

/**
 * Initializes the logging system to capture future calls to `aws_log` and `aws_vlog`. The settings here are shared amongst
 * all other instances of `aws_thread` when `aws_thread_launch` is called.
 */
AWS_COMMON_API int aws_log_system_init(struct aws_allocator *alloc, size_t max_message_len, int memory_pool_message_count, int max_message_count, enum aws_log_level level);

/**
 * TODO (randgaul): Document this.
 */
AWS_COMMON_API void aws_log_system_set_level(enum aws_log_level level);

/**
 * TODO (randgaul): Document this.
 */
AWS_COMMON_API enum aws_log_level aws_log_system_get_level(void);

/**
 * Cleans up all logging related resources and flushes any remaining logs.
 */
AWS_COMMON_API void aws_log_system_clean_up();

/**
 * Records a log entry to be processed by a later call to `aws_log_flush`.
 */
AWS_COMMON_API int aws_log(enum aws_log_level level, const char *tag, const char *fmt, ...);

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
 * or by any other means deemed necessary.
 */
AWS_COMMON_API int aws_log_flush();

/**
 * TODO (randgaul): Document this.
 */
AWS_COMMON_API int aws_log_spawn_log_thread();

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_LOG_H */
