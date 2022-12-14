/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/log_writer.h>
#include <aws/common/logging.h>

#include <aws/common/string.h>

#include <errno.h>
#include <inttypes.h>
#include <stdio.h>

/*
 * Basic log writer implementations - stdout, stderr, arbitrary file
 */

struct aws_file_writer;

struct aws_file_writer {
    FILE *log_file;
    bool close_file_on_cleanup;
    struct aws_logger_file_roll_config roll_config;

    int64_t current_file_length;
    struct aws_string *filename;
};

static bool s_should_roll_logs(const struct aws_file_writer *writer) {
    if (!writer->close_file_on_cleanup) {
        return false;
    }

    if (writer->roll_config.roll_file_count == 0 || writer->roll_config.maximum_file_size == 0) {
        return false;
    }

    if (writer->current_file_length < writer->roll_config.maximum_file_size) {
        return false;
    }

    return true;
}

#define MAX_UINT32_LENGTH 10

static struct aws_string *s_compute_rolled_filename(
    struct aws_allocator *allocator,
    const struct aws_string *filename,
    uint32_t index) {
    char buffer[4096];

    snprintf(buffer, sizeof(buffer), "%s%" PRIu32, filename->bytes, index);

    return aws_string_new_from_c_str(allocator, buffer);
}

AWS_STATIC_STRING_FROM_LITERAL(s_append_mode, "a+");
AWS_STATIC_STRING_FROM_LITERAL(s_write_mode, "w");

static int s_roll_logs(struct aws_log_writer *file_writer) {
    struct aws_file_writer *writer = (struct aws_file_writer *)file_writer->impl;
    struct aws_allocator *allocator = file_writer->allocator;

    /*
     * Suppose that roll_file_count is N.
     * There is one active log file: logfile
     * There are up to N rolled files, from youngest to oldest: logfile1, ..., logfileN
     */
    struct aws_string *source_filename = NULL;
    struct aws_string *dest_filename = NULL;
    uint32_t roll_file_count = writer->roll_config.roll_file_count;
    int result = AWS_OP_ERR;

    /* delete last rolled file, logfileN, if it exists */
    source_filename = s_compute_rolled_filename(allocator, writer->filename, writer->roll_config.roll_file_count);
    if (aws_file_delete(source_filename)) {
        goto done;
    }

    /*
     * From oldest to youngest, move each preceding rolled file up one rank.  Nonexistence is not an error.
     *
     * logfileN-1 -> logfileN, .... , logfile1 -> logfile2
     */
    for (uint32_t i = 1; i < roll_file_count; ++i) {
        uint32_t source_index = roll_file_count - i;

        aws_string_destroy(dest_filename);
        dest_filename = source_filename;
        source_filename = s_compute_rolled_filename(allocator, writer->filename, source_index);

        if (aws_path_exists(source_filename)) {
            if (aws_directory_or_file_move(source_filename, dest_filename)) {
                goto done;
            }
        }
    }

    /* close current log file */
    fclose(writer->log_file);
    writer->log_file = NULL;

    /* move current logfile to logfile1 */
    aws_string_destroy(dest_filename);
    dest_filename = source_filename;
    source_filename = NULL;
    if (aws_directory_or_file_move(writer->filename, dest_filename)) {
        goto done;
    }

    /* create a new logfile */
    writer->log_file = aws_fopen_safe(writer->filename, s_write_mode);
    if (writer->log_file == NULL) {
        aws_translate_and_raise_io_error(errno);
        goto done;
    }

    writer->current_file_length = 0;

    result = AWS_OP_SUCCESS;

done:

    aws_string_destroy(source_filename);
    aws_string_destroy(dest_filename);

    return result;
}

static int s_aws_file_writer_write(struct aws_log_writer *writer, const struct aws_string *output) {
    struct aws_file_writer *impl = (struct aws_file_writer *)writer->impl;

    if (s_should_roll_logs(impl)) {
        if (s_roll_logs(writer)) {
            return AWS_OP_ERR;
        }
    }
    size_t length = output->len;
    if (fwrite(output->bytes, 1, length, impl->log_file) < length) {
        return aws_translate_and_raise_io_error(errno);
    }

    return AWS_OP_SUCCESS;
}

static void s_aws_file_writer_clean_up(struct aws_log_writer *writer) {
    struct aws_file_writer *impl = (struct aws_file_writer *)writer->impl;

    if (impl->close_file_on_cleanup) {
        fclose(impl->log_file);
    }

    aws_string_destroy(impl->filename);

    aws_mem_release(writer->allocator, impl);
}

static struct aws_log_writer_vtable s_aws_file_writer_vtable = {
    .write = s_aws_file_writer_write,
    .clean_up = s_aws_file_writer_clean_up,
};

static int s_set_up_log_file(
    struct aws_file_writer *writer,
    struct aws_allocator *allocator,
    struct aws_log_writer_file_options *options) {

    if (options->file != NULL) {
        writer->log_file = options->file;
        return AWS_OP_SUCCESS;
    }

    writer->filename = aws_string_new_from_c_str(allocator, options->filename);
    writer->log_file = aws_fopen_safe(writer->filename, s_append_mode);
    if (writer->log_file == NULL) {
        return aws_translate_and_raise_io_error(errno);
    }

    writer->close_file_on_cleanup = true;

    if (aws_file_get_length(writer->log_file, &writer->current_file_length)) {
        return AWS_OP_ERR;
    }

    if (options->roll_options) {
        writer->roll_config = *options->roll_options;
    }

    return AWS_OP_SUCCESS;
}

/*
 * Shared internal init implementation
 */
static int s_aws_file_writer_init_internal(
    struct aws_log_writer *writer,
    struct aws_allocator *allocator,
    struct aws_log_writer_file_options *options) {

    /* One or the other should be set */
    if (!((options->filename != NULL) ^ (options->file != NULL))) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    /* Allocate and initialize the file writer */
    struct aws_file_writer *impl = aws_mem_calloc(allocator, 1, sizeof(struct aws_file_writer));
    if (impl == NULL) {
        return AWS_OP_ERR;
    }

    writer->vtable = &s_aws_file_writer_vtable;
    writer->allocator = allocator;
    writer->impl = impl;

    if (s_set_up_log_file(impl, allocator, options)) {
        goto on_error;
    }

    return AWS_OP_SUCCESS;

on_error:

    s_aws_file_writer_clean_up(writer);

    return AWS_OP_ERR;
}

/*
 * Public initialization interface
 */
int aws_log_writer_init_stdout(struct aws_log_writer *writer, struct aws_allocator *allocator) {
    struct aws_log_writer_file_options options = {
        .file = stdout,
    };
    return s_aws_file_writer_init_internal(writer, allocator, &options);
}

int aws_log_writer_init_stderr(struct aws_log_writer *writer, struct aws_allocator *allocator) {
    struct aws_log_writer_file_options options = {
        .file = stderr,
    };

    return s_aws_file_writer_init_internal(writer, allocator, &options);
}

int aws_log_writer_init_file(
    struct aws_log_writer *writer,
    struct aws_allocator *allocator,
    struct aws_log_writer_file_options *options) {

    return s_aws_file_writer_init_internal(writer, allocator, options);
}

void aws_log_writer_clean_up(struct aws_log_writer *writer) {
    AWS_ASSERT(writer->vtable->clean_up);
    (writer->vtable->clean_up)(writer);
}
