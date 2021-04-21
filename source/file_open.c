/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file_open.h>
#include <stdio.h>
#include <windows.h>

FILE *aws_fopen(const char *file_path, const char *mode) {

#ifdef _WIN32
    wchar_t w_file_path[1000];

    MultiByteToWideChar(0, 0, file_path, -1, w_file_path, (int)(strlen(file_path) + 1));
    wchar_t w_mode[10];
    MultiByteToWideChar(0, 0, mode, -1, w_mode, (int)(strlen(mode) + 1));
    FILE *file;
    if (_wfopen_s(&file, w_file_path, w_mode)) {
        return NULL;
    }
    return file;
#else
    return fopen(file_path, mode);
#endif
}
