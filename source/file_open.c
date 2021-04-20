/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file_open.h>

FILE *aws_fopen(const char *file_path, const char *mode) {

#ifdef _WIN32
    wchar_t * w_file_path = new wchar_t[strlen(file_path)+1];
    mbstowcs_s(NULL,w_file_path,strlen(file_path)+1,file_path,strlen(file_path));
    return _wfopen(w_file_path, mode);
#else
    return fopen(file_path, mode);
#endif
}
