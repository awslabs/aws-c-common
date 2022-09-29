/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/log_writer.h>

#include <aws/common/string.h>

#include <errno.h>
#include <stdio.h>

/*
 * Basic log writer implementations - stdout, stderr, arbitrary file
 */

struct aws_file_writer;

struct aws_file_writer {
    size_t current_log_file_bytes;
    size_t maximum_log_file_bytes;
    int next_log_file_index;
    int maximum_log_index;
    struct aws_string *file_name_base;
    FILE *log_file;
    bool close_file_on_cleanup;
};

static struct aws_string *s_compute_log_file_name(struct aws_file_writer *writer, struct aws_allocator *allocator) {

    if (writer->maximum_log_index > 0) {
        char name_buffer[512];
        snprintf(
            name_buffer,
            AWS_ARRAY_SIZE(name_buffer),
            "%s%d",
            aws_string_c_str(writer->file_name_base),
            writer->next_log_file_index);

        return aws_string_new_from_array(allocator, (const uint8_t *)name_buffer, AWS_ARRAY_SIZE(name_buffer));
    } else {
        return aws_string_new_from_string(allocator, writer->file_name_base);
    }
}

static int s_aws_file_writer_create_file(struct aws_file_writer *file_writer, struct aws_allocator *allocator) {
    file_writer->current_log_file_bytes = 0;

    struct aws_string *file_name = s_compute_log_file_name(file_writer, allocator);
    if (file_name == NULL) {
        return AWS_OP_ERR;
    }

    if (file_writer->maximum_log_index > 0) {
        file_writer->next_log_file_index++;
        if (file_writer->next_log_file_index > file_writer->maximum_log_index) {
            file_writer->next_log_file_index = 0;
        }
    }

    file_writer->log_file = aws_fopen(aws_string_c_str(file_name), "w+");
    aws_string_destroy(file_name);

    if (file_writer->log_file == NULL) {
        return aws_translate_and_raise_io_error(errno);
    }

    return AWS_OP_SUCCESS;
}

static int s_aws_file_writer_write(struct aws_log_writer *writer, const struct aws_string *output) {
    struct aws_file_writer *impl = (struct aws_file_writer *)writer->impl;

    if (impl->log_file == NULL) {
        if (s_aws_file_writer_create_file(impl, writer->allocator)) {
            return AWS_OP_ERR;
        }
    }

    size_t length = output->len;
    size_t bytes_written = fwrite(output->bytes, 1, length, impl->log_file);
    impl->current_log_file_bytes += bytes_written;

    if (impl->maximum_log_file_bytes > 0 && impl->current_log_file_bytes >= impl->maximum_log_file_bytes) {
        if (impl->close_file_on_cleanup) {
            fclose(impl->log_file);
            impl->log_file = NULL;
        }
    }

    if (bytes_written < length) {
        return aws_translate_and_raise_io_error(errno);
    }

    return AWS_OP_SUCCESS;
}

static void s_aws_file_writer_clean_up(struct aws_log_writer *writer) {
    struct aws_file_writer *impl = (struct aws_file_writer *)writer->impl;

    if (impl->close_file_on_cleanup) {
        fclose(impl->log_file);
    }

    aws_string_destroy(impl->file_name_base);

    aws_mem_release(writer->allocator, impl);
}

static struct aws_log_writer_vtable s_aws_file_writer_vtable = {
    .write = s_aws_file_writer_write,
    .clean_up = s_aws_file_writer_clean_up,
};

/*
 * Shared internal init implementation
 */
static int s_aws_file_writer_init_internal(
    struct aws_log_writer *writer,
    struct aws_allocator *allocator,
    const char *file_name_to_open,
    FILE *currently_open_file,
    int maximum_log_file_index) {

    /* One or the other should be set */
    if (!((file_name_to_open != NULL) ^ (currently_open_file != NULL))) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    /* Allocate and initialize the file writer */
    struct aws_file_writer *impl = aws_mem_calloc(allocator, 1, sizeof(struct aws_file_writer));
    if (impl == NULL) {
        return AWS_OP_ERR;
    }

    impl->log_file = NULL;
    impl->close_file_on_cleanup = false;

    /* Open file if name passed in */
    if (file_name_to_open != NULL) {
        impl->file_name_base = aws_string_new_from_c_str(allocator, file_name_to_open);
        impl->close_file_on_cleanup = true;

        impl->maximum_log_index = maximum_log_file_index;
        if (maximum_log_file_index > 0) {
            impl->maximum_log_file_bytes = 1000000000;
        }

        if (s_aws_file_writer_create_file(impl, allocator)) {
            aws_string_destroy(impl->file_name_base);
            aws_mem_release(allocator, impl);
            return AWS_OP_ERR;
        }
    } else {
        impl->log_file = currently_open_file;
    }

    writer->vtable = &s_aws_file_writer_vtable;
    writer->allocator = allocator;
    writer->impl = impl;

    return AWS_OP_SUCCESS;
}

/*
 * Public initialization interface
 */
int aws_log_writer_init_stdout(struct aws_log_writer *writer, struct aws_allocator *allocator) {
    return s_aws_file_writer_init_internal(writer, allocator, NULL, stdout, 0);
}

int aws_log_writer_init_stderr(struct aws_log_writer *writer, struct aws_allocator *allocator) {
    return s_aws_file_writer_init_internal(writer, allocator, NULL, stderr, 0);
}

int aws_log_writer_init_file(
    struct aws_log_writer *writer,
    struct aws_allocator *allocator,
    struct aws_log_writer_file_options *options) {
    return s_aws_file_writer_init_internal(
        writer, allocator, options->filename, options->file, options->maximum_log_file_index);
}

void aws_log_writer_clean_up(struct aws_log_writer *writer) {
    AWS_ASSERT(writer->vtable->clean_up);
    (writer->vtable->clean_up)(writer);
}
