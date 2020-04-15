/*
 * Copyright 2010-2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/process.h>
#include <aws/common/string.h>

#include <stdio.h>
#include <sys/types.h>

#define MAX_BUFFER_SIZE (2048)
struct aws_run_command_result *aws_run_command_result_new(struct aws_allocator *allocator) {
    if (!allocator) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }
    struct aws_run_command_result *result = aws_mem_calloc(allocator, 1, sizeof(struct aws_run_command_result));
    if (!result) {
        return NULL;
    }
    result->allocator = allocator;
    return result;
}

void aws_run_command_result_destroy(struct aws_run_command_result *result) {
    if (!result) {
        return;
    }
    aws_string_destroy_secure(result->std_out);
    aws_string_destroy_secure(result->std_err);
    aws_mem_release(result->allocator, result);
}

struct aws_run_command_result *aws_run_command(struct aws_run_command_options options) {
    FILE *output_stream;
    char output_buffer[MAX_BUFFER_SIZE];
    struct aws_run_command_result *result = aws_run_command_result_new(options.allocator);
    if (!result) {
        return NULL;
    }

#ifdef _WIN32
    output_stream = _popen(options.command, "r");
#else
    output_stream = popen(options.command, "r");
#endif

    struct aws_byte_buf result_buffer;
    if (aws_byte_buf_init(&result_buffer, result->allocator, MAX_BUFFER_SIZE)) {
        goto on_finish;
    }

    if (output_stream) {
        while (!feof(output_stream)) {
            if (fgets(output_buffer, MAX_BUFFER_SIZE, output_stream) != NULL) {
                struct aws_byte_cursor cursor = aws_byte_cursor_from_c_str(output_buffer);
                if (aws_byte_buf_append_dynamic(&result_buffer, &cursor)) {
                    goto on_finish;
                }
            }
        }
#ifdef _WIN32
        _pclose(output_stream);
#else
        pclose(output_stream);
#endif
    }

    struct aws_byte_cursor trim_cursor = aws_byte_cursor_from_buf(&result_buffer);
    struct aws_byte_cursor trimmed_cursor = aws_byte_cursor_trim_pred(&trim_cursor, aws_char_is_space);
    result->std_out = aws_string_new_from_array(result->allocator, trimmed_cursor.ptr, trimmed_cursor.len);

on_finish:
    aws_byte_buf_clean_up_secure(&result_buffer);
    return result;
}
