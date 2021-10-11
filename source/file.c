/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/file.h>
#include <aws/common/logging.h>
#include <aws/common/string.h>

#include <errno.h>

FILE* aws_fopen(const char* file_path, const char* mode) {
    struct aws_string* file_path_str = aws_string_new_from_c_str(aws_default_allocator(), file_path);
    struct aws_string* mode_str = aws_string_new_from_c_str(aws_default_allocator(), mode);

    FILE* file = aws_fopen_safe(file_path_str, mode_str);
    aws_string_destroy(mode_str);
    aws_string_destroy(file_path_str);

    return file;
}

int aws_byte_buf_init_from_file(struct aws_byte_buf * out_buf, struct aws_allocator * alloc, const char *filename) {
        AWS_ZERO_STRUCT(*out_buf);
        FILE *fp = aws_fopen(filename, "rb");

        if (fp) {
            if (fseek(fp, 0L, SEEK_END)) {
                AWS_LOGF_ERROR(AWS_LS_COMMON_IO, "static: Failed to seek file %s with errno %d", filename, errno);
                fclose(fp);
                return aws_translate_and_raise_io_error(errno);
            }

            size_t allocation_size = (size_t)ftell(fp) + 1;
            /* Tell the user that we allocate here and if success they're responsible for the free. */
            if (aws_byte_buf_init(out_buf, alloc, allocation_size)) {
                fclose(fp);
                return AWS_OP_ERR;
            }

            /* Ensure compatibility with null-terminated APIs, but don't consider
             * the null terminator part of the length of the payload */
            out_buf->len = out_buf->capacity - 1;
            out_buf->buffer[out_buf->len] = 0;

            if (fseek(fp, 0L, SEEK_SET)) {
                AWS_LOGF_ERROR(AWS_LS_COMMON_IO, "static: Failed to seek file %s with errno %d", filename, errno);
                aws_byte_buf_clean_up(out_buf);
                fclose(fp);
                return aws_translate_and_raise_io_error(errno);
            }

            size_t read = fread(out_buf->buffer, 1, out_buf->len, fp);
            fclose(fp);
            if (read < out_buf->len) {
                AWS_LOGF_ERROR(AWS_LS_COMMON_IO, "static: Failed to read file %s with errno %d", filename, errno);
                aws_secure_zero(out_buf->buffer, out_buf->len);
                aws_byte_buf_clean_up(out_buf);
                return aws_raise_error(AWS_ERROR_SYS_CALL_FAILURE);
            }

            return AWS_OP_SUCCESS;
        }

        AWS_LOGF_ERROR(AWS_LS_COMMON_IO, "static: Failed to open file %s with errno %d", filename, errno);

        return aws_translate_and_raise_io_error(errno);
    }

    bool aws_is_any_directory_separator(char value) {
        return value == '\\' || value == '/';
    }
