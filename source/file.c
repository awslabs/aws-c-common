/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/string.h>

FILE *aws_fopen(const char *file_path, const char *mode) {
    struct aws_string *file_path_str = aws_string_new_from_c_str(aws_default_allocator(), file_path);
    struct aws_string *mode_str = aws_string_new_from_c_str(aws_default_allocator(), mode);

    FILE *file = aws_fopen_safe(file_path_str, mode_str);
    aws_string_destroy(mode_str);
    aws_string_destroy(file_path_str);

    return file;
}
