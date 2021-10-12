#ifndef AWS_COMMON_FILE_H
#define AWS_COMMON_FILE_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

#include <stdio.h>

AWS_EXTERN_C_BEGIN

/**
 * To support non-ascii file path across platform.
 * For windows, _wfopen will be invoked under the hood. For other platforms, same as calling fopen
 * Functionality is the same as fopen.
 * On error, errno will be set, and NULL will be returned. Same as fopen.
 */
AWS_COMMON_API
FILE *aws_fopen(const char *file_path, const char *mode);

/**
 * Returns true iff the character is a directory separator on ANY supported platform.
 */
AWS_COMMON_API
bool aws_is_any_directory_separator(char value);

/**
 * Returns the directory separator used by the local platform
 */
AWS_COMMON_API
char aws_get_platform_directory_separator(void);

/**
 * Returns the current user's home directory.
 */
AWS_COMMON_API
struct aws_string *aws_get_home_directory(struct aws_allocator *allocator);

/**
 * Returns true if a file or path exists, otherwise, false.
 */
AWS_COMMON_API
bool aws_path_exists(const char *path);

/*
 * Wrapper for highest-resolution platform-dependent seek implementation.
 * Maps to:
 *
 *   _fseeki64() on windows
 *   fseeko() on linux
 *
 * whence can either be SEEK_SET or SEEK_END
 */
AWS_COMMON_API
int aws_fseek(FILE *file, int64_t offset, int whence);

/*
 * Wrapper for os-specific file length query.  We can't use fseek(END, 0)
 * because support for it is not technically required.
 *
 * Unix flavors call fstat, while Windows variants use GetFileSize on a
 * HANDLE queried from the libc FILE pointer.
 */
AWS_COMMON_API
int aws_file_get_length(FILE *file, int64_t *length);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FILE_H */
