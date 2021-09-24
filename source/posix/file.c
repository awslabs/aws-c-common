/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/environment.h>
#include <aws/common/file.h>
#include <aws/common/string.h>
#include <errno.h>
#include <stdio.h>
#include <sys/stat.h>

FILE *aws_fopen(const char *file_path, const char *mode) {
    return fopen(file_path, mode);
}

char aws_get_platform_directory_separator(void) {
    return '/';
}

AWS_STATIC_STRING_FROM_LITERAL(s_home_env_var, "HOME");

struct aws_string *aws_get_home_directory(struct aws_allocator *allocator) {

    /* ToDo: check getpwuid_r if environment check fails */
    struct aws_string *home_env_var_value = NULL;
    if (aws_get_environment_value(allocator, s_home_env_var, &home_env_var_value) == 0 && home_env_var_value != NULL) {
        return home_env_var_value;
    }

    return NULL;
}

bool aws_path_exists(const char *path) {
    struct stat buffer;
    return stat(path, &buffer) == 0;
}

int aws_fseek(FILE *file, int64_t offset, int whence) {

#ifdef AWS_HAVE_POSIX_LARGE_FILE_SUPPORT
    int result = fseeko(file, offset, whence);
#else
    /* must use fseek(), which takes offset as a long */
    if (offset < LONG_MIN || offset > LONG_MAX) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    int result = fseek(file, offset, whence);
#endif /* AWS_HAVE_POSIX_LFS */

    if (result != 0) {
        return aws_translate_and_raise_io_error(errno);
    }

    return AWS_OP_SUCCESS;
}

int aws_file_get_length(FILE *file, int64_t *length) {

    struct stat file_stats;

    int fd = fileno(file);
    if (fd == -1) {
        return aws_raise_error(AWS_ERROR_INVALID_FILE_HANDLE);
    }

    if (fstat(fd, &file_stats)) {
        return aws_translate_and_raise_io_error(errno);
    }

    *length = file_stats.st_size;

    return AWS_OP_SUCCESS;
}
