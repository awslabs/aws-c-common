#ifndef AWS_COMMON_FILE_H
#define AWS_COMMON_FILE_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

/**
 * To support non-ascii file path across platform.
 * For windows, _wfopen will be invoked under the hood. For other platforms, same as calling fopen
 * Functionality is the same as fopen.
 * On error, errno will be set, and NULL will be returned. Same as fopen.
 */
AWS_COMMON_API
FILE *aws_fopen(const char *file_path, const char *mode);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FILE_H */
