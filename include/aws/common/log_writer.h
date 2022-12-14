
#ifndef AWS_COMMON_LOG_WRITER_H
#define AWS_COMMON_LOG_WRITER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

struct aws_allocator;
struct aws_string;

/*
 * Log writer interface and default implementation(s)
 *
 * A log writer functions as a sink for formatted log lines.  We provide
 * default implementations that go to stdout, stderr, and a specified file.
 */
struct aws_log_writer;

typedef int(aws_log_writer_write_fn)(struct aws_log_writer *writer, const struct aws_string *output);
typedef void(aws_log_writer_clean_up_fn)(struct aws_log_writer *writer);

struct aws_log_writer_vtable {
    aws_log_writer_write_fn *write;
    aws_log_writer_clean_up_fn *clean_up;
};

struct aws_log_writer {
    struct aws_log_writer_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

/**
 * Log rolling is only supported when logging to a file created by the logger (not stdout, stderr)
 *
 * The current log file will use the configured filename.
 *
 * Rolled log files will have a number appended to the end of their name, the bigger the number, the older the logs.
 */
struct aws_logger_file_roll_config {

    /*
     * Maximum number of additional "rolled" log files to create.
     *
     * If this is zero, log rolling will not be done.
     */
    uint32_t roll_file_count;

    /*
     * Maximum size per log file (and rolled log files).  When the current log file exceeds this size, all logs
     * will be rolled:
     *
     * filename -> filename1 -> filename2 -> ... -> filenameN
     *
     * and a new current log file will be created.
     */
    int64_t maximum_file_size;
};

struct aws_log_writer_file_options {
    const char *filename;
    FILE *file;
    struct aws_logger_file_roll_config *roll_options;
};

AWS_EXTERN_C_BEGIN

/*
 * Initialize a log writer that sends log lines to stdout.  Uses C library IO.
 */
AWS_COMMON_API
int aws_log_writer_init_stdout(struct aws_log_writer *writer, struct aws_allocator *allocator);

/*
 * Initialize a log writer that sends log lines to stderr.  Uses C library IO.
 */
AWS_COMMON_API
int aws_log_writer_init_stderr(struct aws_log_writer *writer, struct aws_allocator *allocator);

/*
 * Initialize a log writer that sends log lines to a file.  Uses C library IO.
 */
AWS_COMMON_API
int aws_log_writer_init_file(
    struct aws_log_writer *writer,
    struct aws_allocator *allocator,
    struct aws_log_writer_file_options *options);

/*
 * Frees all resources used by a log writer with the exception of the base structure memory
 */
AWS_COMMON_API
void aws_log_writer_clean_up(struct aws_log_writer *writer);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_LOG_WRITER_H */
