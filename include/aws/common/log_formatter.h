
#ifndef AWS_COMMON_LOG_FORMATTER_H
#define AWS_COMMON_LOG_FORMATTER_H

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

#include <aws/common/date_time.h>
#include <aws/common/logging.h>

#include <stdarg.h>
#include <stdio.h>

struct aws_allocator;
struct aws_string;

/*
 * Log formatter interface and default implementation
 *
 * Log formatters are invoked by the LOGF_* macros to transform a set of arguments into
 * one or more lines of text to be output to a logging sink (writer).
 */
struct aws_log_formatter;

typedef int(aws_log_formatter_format_fn)(
    struct aws_log_formatter *formatter,
    struct aws_string **formatted_output,
    enum aws_log_level level,
    aws_log_subject_t subject,
    const char *format,
    va_list args);

typedef void(aws_log_formatter_clean_up_fn)(struct aws_log_formatter *logger);

struct aws_log_formatter_vtable {
    aws_log_formatter_format_fn *format;
    aws_log_formatter_clean_up_fn *clean_up;
};

struct aws_log_formatter {
    struct aws_log_formatter_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

struct aws_log_formatter_standard_options {
    enum aws_date_format date_format;
};

AWS_EXTERN_C_BEGIN

/*
 * Initializes the default log formatter which outputs lines in the format:
 *
 *   [<LogLevel>] [<Timestamp>] [<ThreadId>] - <User content>\n
 */
AWS_COMMON_API
int aws_log_formatter_init_default(
    struct aws_log_formatter *formatter,
    struct aws_allocator *allocator,
    struct aws_log_formatter_standard_options *options);

/*
 * Cleans up a log formatter (minus the base structure memory) by calling the formatter's clean_up function
 * via the vtable.
 */
AWS_COMMON_API
void aws_log_formatter_clean_up(struct aws_log_formatter *formatter);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_LOG_FORMATTER_H */
