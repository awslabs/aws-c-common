/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#define _GNU_SOURCE /* NOLINT(bugprone-reserved-identifier) */

#include <aws/common/environment.h>
#include <aws/common/file.h>
#include <aws/common/logging.h>
#include <aws/common/string.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <pwd.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

/* O_DIRECT is not available on all platforms */
#ifndef O_DIRECT
#    define O_DIRECT 0
#endif

int aws_file_path_read_from_offset_direct_io(
    const struct aws_string *file_path,
    uint64_t offset,
    size_t max_read_length,
    struct aws_byte_buf *output_buf,
    size_t *out_actual_read) {

    if (O_DIRECT == 0) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_GENERAL, "O_DIRECT is not supported on this platform");
        return aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
    }

    size_t available_len = aws_sub_size_saturating(output_buf->capacity, output_buf->len);
    size_t length = aws_min_size(available_len, max_read_length);
    if (length == 0) {
        return AWS_OP_SUCCESS; /* Nothing to do. */
    }

    int rt_code = AWS_OP_ERR;
    int fd = open(aws_string_c_str(file_path), O_RDONLY | O_DIRECT);
    if (fd == -1) {
        int errno_value = errno; /* Always cache errno before potential side-effect */
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "Failed to open file %s for reading with O_DIRECT, errno: %d",
            aws_string_c_str(file_path),
            errno_value);
        aws_translate_and_raise_io_error(errno_value);
        goto cleanup;
    }

    /* seek to the right position and then read */
    if (lseek(fd, (off_t)offset, SEEK_SET) == -1) {
        int errno_value = errno; /* Always cache errno before potential side-effect */
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "Failed to seek to position %llu in file %s, errno: %d",
            (unsigned long long)offset,
            aws_string_c_str(file_path),
            errno_value);
        aws_translate_and_raise_io_error(errno_value);
        goto cleanup;
    }

    ssize_t bytes_read = read(fd, output_buf->buffer, length);
    if (bytes_read == -1) {
        int errno_value = errno; /* Always cache errno before potential side-effect */
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "Failed to read %zu bytes from file %s, errno: %d",
            length,
            aws_string_c_str(file_path),
            errno_value);
        aws_translate_and_raise_io_error(errno_value);
        goto cleanup;
    }

    *out_actual_read = (size_t)bytes_read;
    output_buf->len += bytes_read;
    rt_code = AWS_OP_SUCCESS;
cleanup:
    if (fd != -1) {
        close(fd);
    }
    return rt_code;
}
