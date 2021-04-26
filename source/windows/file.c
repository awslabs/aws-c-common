/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <stdio.h>
#include <windows.h>

FILE *aws_fopen(const char *file_path, const char *mode) {

    wchar_t w_file_path[1000];

    /* the default encoding is utf-8 or ascii */
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, file_path, -1, w_file_path, AWS_ARRAY_SIZE(w_file_path))) {
        /* When error happens, we need to set errno to invalid argument, since the function will set the Windows
         * specific error that we don't handle */
        errno = EINVAL;
        return NULL;
    }
    wchar_t w_mode[10];
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, mode, -1, w_mode, AWS_ARRAY_SIZE(w_mode))) {
        errno = EINVAL;
        return NULL;
    }
    FILE *file;
    if (_wfopen_s(&file, w_file_path, w_mode)) {
        /* errno will be set */
        return NULL;
    }
    return file;
}
