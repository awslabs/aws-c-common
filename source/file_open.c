/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file_open.h>
#include <stdio.h>
#ifdef _WIN32
    #include <windows.h>
#endif

FILE *aws_fopen(const char *file_path, const char *mode) {

#ifdef _WIN32
    wchar_t w_file_path[1000];

    /* the default encoding is utf-8 or ascii */
    MultiByteToWideChar(CP_UTF8, 0, file_path, -1, w_file_path, (int)(strlen(file_path) + 1));
    wchar_t w_mode[10];
    MultiByteToWideChar(CP_UTF8, 0, mode, -1, w_mode, (int)(strlen(mode) + 1));
    FILE *file;
    if (_wfopen_s(&file, w_file_path, w_mode)) {
        return NULL;
    }
    return file;
#else
    return fopen(file_path, mode);
#endif
}
