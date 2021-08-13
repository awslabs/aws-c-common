/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/string.h>

#include <stdio.h>

#include <dirent.h>
#include <errno.h>
#include <sys/stat.h>
#include <unistd.h>

FILE *aws_fopen(const char *file_path, const char *mode) {
    return fopen(file_path, mode);
}

static int s_parse_and_raise_error(int errno_cpy) {
    if (errno_cpy == 0) {
        return AWS_OP_SUCCESS;
    }

    if (errno_cpy == ENOENT || errno_cpy == ENOTDIR) {
        return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    }

    if (errno_cpy == EMFILE || errno_cpy == ENFILE) {
        return aws_raise_error(AWS_ERROR_MAX_FDS_EXCEEDED);
    }

    if (errno_cpy == EACCES) {
        return aws_raise_error(AWS_ERROR_NO_PERMISSION);
    }

    if (errno_cpy == ENOTEMPTY) {
        return aws_raise_error(AWS_ERROR_DIRECTORY_NOT_EMPTY);
    }

    return aws_raise_error(AWS_ERROR_UNKNOWN);
}

int aws_directory_create(struct aws_string *path) {
    int mkdir_ret = mkdir(aws_string_c_str(path), S_IRWXU | S_IRWXG | S_IRWXO);

    /** nobody cares if it already existed. */
    if (mkdir_ret != 0 && errno != EEXIST) {
        return s_parse_and_raise_error(errno);
    }

    return AWS_OP_SUCCESS;
}

bool aws_directory_exists(struct aws_string *dir_path) {
    struct stat dir_info;
    if (lstat(aws_string_c_str(dir_path), &dir_info) == 0 && S_ISDIR(dir_info.st_mode)) {
        return true;
    }

    return false;
}

static bool s_delete_file_or_directory(const struct aws_directory_entry *entry, void *user_data) {
    struct aws_allocator *allocator = user_data;

    struct aws_string *path_str = aws_string_new_from_cursor(allocator, &entry->relative_path);
    int ret_val = AWS_OP_SUCCESS;

    if (entry->file_type & AWS_FILE_TYPE_FILE) {
        ret_val = aws_file_delete(path_str);
    }

    if (entry->file_type & AWS_FILE_TYPE_DIRECTORY) {
        ret_val = aws_directory_delete(path_str, allocator, false);
    }

    aws_string_destroy(path_str);
    return ret_val == AWS_OP_SUCCESS;
}

int aws_directory_delete(struct aws_string *dir_path, struct aws_allocator *allocator, bool recursive) {
    int ret_val = AWS_OP_SUCCESS;

    if (recursive) {
        ret_val = aws_directory_traverse(allocator, dir_path, true, s_delete_file_or_directory, allocator);
    }

    if (ret_val) {
        return AWS_OP_ERR;
    }

    int error_code = rmdir(aws_string_c_str(dir_path));

    return error_code == 0 ? AWS_OP_SUCCESS : s_parse_and_raise_error(errno);
}

int aws_directory_or_file_move(struct aws_string *from, struct aws_string *to) {
    int error_code = rename(aws_string_c_str(from), aws_string_c_str(to));

    return error_code == 0 ? AWS_OP_SUCCESS : s_parse_and_raise_error(errno);
}

int aws_file_delete(struct aws_string *file_path) {
    int error_code = unlink(aws_string_c_str(file_path));
    return error_code == 0 ? AWS_OP_SUCCESS : s_parse_and_raise_error(errno);
}

int aws_directory_traverse(
    struct aws_allocator *allocator,
    struct aws_string *path,
    bool recursive,
    aws_on_directory_entry *on_entry,
    void *user_data) {
    DIR *dir = opendir(aws_string_c_str(path));

    if (!dir) {
        return s_parse_and_raise_error(errno);
    }

    struct aws_byte_cursor current_path = aws_byte_cursor_from_string(path);
    if (current_path.ptr[current_path.len - 1] == AWS_PATH_DELIM) {
        current_path.len -= 1;
    }

    struct dirent *dirent = NULL;
    int ret_val = AWS_ERROR_SUCCESS;

    errno = 0;
    while ((dirent = readdir(dir)) != NULL) {
        /* note: dirent->name_len is only defined on the BSDs, but not linux. It's not in the
         * required posix spec. So we use dirent->d_name as a c string here. */
        struct aws_byte_cursor name_component = aws_byte_cursor_from_c_str(dirent->d_name);

        if (aws_byte_cursor_eq_c_str(&name_component, "..") || aws_byte_cursor_eq_c_str(&name_component, ".")) {
            continue;
        }

        struct aws_byte_buf relative_path;
        aws_byte_buf_init_copy_from_cursor(&relative_path, allocator, current_path);
        aws_byte_buf_append_byte_dynamic(&relative_path, AWS_PATH_DELIM);
        aws_byte_buf_append_dynamic(&relative_path, &name_component);
        aws_byte_buf_append_byte_dynamic(&relative_path, 0);
        relative_path.len -= 1;

        struct aws_directory_entry entry;
        AWS_ZERO_STRUCT(entry);

        struct stat dir_info;
        if (!lstat((const char *)relative_path.buffer, &dir_info)) {
            if (S_ISDIR(dir_info.st_mode)) {
                entry.file_type |= AWS_FILE_TYPE_DIRECTORY;
            }
            if (S_ISLNK(dir_info.st_mode)) {
                entry.file_type |= AWS_FILE_TYPE_SYM_LINK;
            }
            if (S_ISREG(dir_info.st_mode)) {
                entry.file_type |= AWS_FILE_TYPE_FILE;
                entry.file_size = dir_info.st_size;
            }

            if (!entry.file_type) {
                AWS_ASSERT("Unknown file type encountered");
            }

            entry.relative_path = aws_byte_cursor_from_buf(&relative_path);
            const char *full_path = realpath((const char *)relative_path.buffer, NULL);

            if (full_path) {
                entry.path = aws_byte_cursor_from_c_str(full_path);
            }

            if (recursive && entry.file_type & AWS_FILE_TYPE_DIRECTORY) {
                struct aws_string *rel_path_str = aws_string_new_from_cursor(allocator, &entry.relative_path);
                ret_val = aws_directory_traverse(allocator, rel_path_str, recursive, on_entry, user_data);
                aws_string_destroy(rel_path_str);
            }

            if (!on_entry(&entry, user_data)) {
                aws_byte_buf_clean_up(&relative_path);
                ret_val = aws_raise_error(AWS_ERROR_OPERATION_INTERUPTED);
                break;
            }

            aws_byte_buf_clean_up(&relative_path);

            if (ret_val) {
                break;
            }
        }
    }

    closedir(dir);
    return ret_val;
}
