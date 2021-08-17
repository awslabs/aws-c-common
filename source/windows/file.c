/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <errno.h>
#include <stdio.h>
#include <windows.h>

FILE *aws_fopen_safe(const aws_string *file_path, const aws_string *mode) {

    struct aws_string *w_file_path = aws_string_convert_to_wchar_str(aws_default_allocator(), file_path);
    struct aws_string *w_mode = aws_string_convert_to_wchar_str(aws_default_allocator(), mode);

    FILE *file = _wfopen_s(&file, aws_string_wchar_c_str(w_file_path), aws_string_wchar_c_str(w_mode));
    /* actually handle the error correctly here. */
    aws_string_destroy(w_mode);
    aws_string_destroy(w_file_path);

    return file;
}
