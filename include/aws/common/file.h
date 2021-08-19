#ifndef AWS_COMMON_FILE_H
#define AWS_COMMON_FILE_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/byte_buf.h>
#include <aws/common/common.h>
#include <aws/common/linked_list.h>
#include <aws/common/ref_count.h>

#ifdef _WIN32
#    define AWS_PATH_DELIM '\\'
#    define AWS_PATH_DELIM_STR "\\"
#else
#    define AWS_PATH_DELIM '/'
#    define AWS_PATH_DELIM_STR "/"
#endif

struct aws_string;

enum aws_file_type {
    AWS_FILE_TYPE_FILE = 1,
    AWS_FILE_TYPE_SYM_LINK = 2,
    AWS_FILE_TYPE_DIRECTORY = 4,
};

struct aws_directory_entry {
    /**
     * Absolute path to the entry from the current process root.
     */
    struct aws_byte_cursor path;
    /**
     * Path to the entry relative to the current working directory.
     */
    struct aws_byte_cursor relative_path;
    /**
     * Bit-field of enum aws_file_type
     */
    int file_type;
    /**
     * Size of the file on disk.
     */
    int64_t file_size;
};

/**
 * Invoked during calls to aws_directory_traverse() as an entry is encountered. entry will contain
 * the parsed directory entry info.
 *
 * Return true to continue the traversal, or alternatively, if you have a reason to abort the traversal, return false.
 */
typedef bool(aws_on_directory_entry)(const struct aws_directory_entry *entry, void *user_data);

AWS_EXTERN_C_BEGIN

/**
 * Don't use this. It never should have been added in the first place. It's now deprecated.
 */
AWS_COMMON_API FILE *aws_fopen(const char *file_path, const char *mode);

/**
 * Opens file at file_path using mode. Returns the FILE pointer if successful.
 */
AWS_COMMON_API FILE *aws_fopen_safe(const struct aws_string *file_path, const struct aws_string *mode);

/**
 * Creates a directory if it doesn't currently exist. If the directory already exists, it's ignored and assumed
 * successful.
 *
 * Returns AWS_OP_SUCCESS on success. Otherwise, check aws_last_error().
 */
AWS_COMMON_API int aws_directory_create(const struct aws_string *dir_path);
/**
 * Returns true if the directory currently exists. Otherwise, it returns false.
 */
AWS_COMMON_API bool aws_directory_exists(const struct aws_string *dir_path);
/**
 * Deletes a directory. If the directory is not empty, this will fail unless the recursive parameter is set to true.
 * If recursive is true then the entire directory and all of its contents will be deleted. If it is set to false,
 * the directory will be deleted only if it is empty. Returns AWS_OP_SUCCESS if the operation was successful. Otherwise,
 * aws_last_error() will contain the error that occurred. If the directory doesn't exist, AWS_OP_SUCCESS is still
 * returned.
 */
AWS_COMMON_API int aws_directory_delete(const struct aws_string *dir_path, bool recursive);
/**
 * Deletes a file. Returns AWS_OP_SUCCESS if the operation was successful. Otherwise,
 * aws_last_error() will contain the error that occurred. If the file doesn't exist, AWS_OP_SUCCESS is still returned.
 */
AWS_COMMON_API int aws_file_delete(const struct aws_string *file_path);

/**
 * Moves directory at from to to.
 * Returns AWS_OP_SUCCESS if the operation was successful. Otherwise,
 * aws_last_error() will contain the error that occurred.
 */
AWS_COMMON_API int aws_directory_or_file_move(const struct aws_string *from, const struct aws_string *to);

/**
 * Traverse a directory starting at path.
 *
 * If you want the traversal to recursive the entire directory, pass recursive as true. Passing false for this parameter
 * will only iterate the contents of the directory, but will not descend into any directories it encounters.
 *
 * If recursive is set to true, the traversal is performed post-order, depth-first
 * (for practical reasons such as deleting a directory that contains subdirectories or files).
 *
 * returns AWS_OP_SUCCESS(0) on success.
 */
AWS_COMMON_API int aws_directory_traverse(
    struct aws_allocator *allocator,
    const struct aws_string *path,
    bool recursive,
    aws_on_directory_entry *on_entry,
    void *user_data);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FILE_H */
