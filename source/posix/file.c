/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/string.h>

#include <stdio.h>

#include <dirent.h>
#include <sys/stat.h>

FILE *aws_fopen(const char *file_path, const char *mode) {
    return fopen(file_path, mode);
}

int aws_directory_entry_open_internal(struct aws_directory_entry *entry) {
    if (entry->impl) {
        return AWS_OP_SUCCESS;
    }

    entry->impl = opendir(aws_string_c_str(entry->path));

    if (!entry->impl) {
        return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    }

    entry->file_type = AWS_FILE_TYPE_DIRECTORY;
    struct dirent *dirent = NULL;

    while ((dirent = readdir(entry->impl)) != NULL) {
        struct aws_byte_cursor name_component = aws_byte_cursor_from_array(dirent->d_name, dirent->d_namlen);

        if (aws_byte_cursor_eq_c_str(&name_component, "..") || aws_byte_cursor_eq_c_str(&name_component, ".")) {
            continue;
        }

        struct aws_byte_buf full_path;
        struct aws_byte_cursor path_component = aws_byte_cursor_from_string(entry->path);
        aws_byte_buf_init_copy_from_cursor(&full_path, entry->allocator, path_component);
        aws_byte_buf_append_byte_dynamic(&full_path, AWS_PATH_DELIM);
        aws_byte_buf_append(&full_path, &name_component);

        struct aws_byte_buf relative_path;
        struct aws_byte_cursor relative_path_component = aws_byte_cursor_from_string(entry->relative_path);
        AWS_ZERO_STRUCT(relative_path);
        aws_byte_buf_init_copy_from_cursor(&relative_path, entry->allocator, relative_path_component);
        aws_byte_buf_append_byte_dynamic(&relative_path, AWS_PATH_DELIM);
        aws_byte_buf_append(&relative_path, &name_component);

        struct aws_byte_cursor path_cur = aws_byte_cursor_from_buf(&full_path);
        struct aws_byte_cursor relative_path_cur = aws_byte_cursor_from_buf(&relative_path);

        struct aws_directory_entry *new_entry =
            aws_directory_entry_open_base(entry->allocator, path_cur, relative_path_cur);
        /* open base set the ref count to one. */
        aws_linked_list_push_back(&entry->children, &new_entry->node);
        new_entry->parent = entry;
        aws_byte_buf_clean_up(&full_path);
        aws_byte_buf_clean_up(&relative_path);

        struct stat dir_info;
        if (!lstat(aws_string_c_str(new_entry->path), &dir_info)) {
            if (S_ISDIR(dir_info.st_mode)) {
                new_entry->file_type = AWS_FILE_TYPE_DIRECTORY;
            } else if (S_ISLNK(dir_info.st_mode)) {
                new_entry->file_type = AWS_FILE_TYPE_SYM_LINK;
            } else if (S_ISREG(dir_info.st_mode)) {
                new_entry->file_type = AWS_FILE_TYPE_FILE;
            } else {
                new_entry->file_type = AWS_FILE_TYPE_NONE;
                AWS_ASSERT("Unknown file type encountered");
            }

            new_entry->file_size = dir_info.st_size;
        }
    }

    return AWS_OP_SUCCESS;
}

void aws_directory_entry_destroy_internal(struct aws_directory_entry *entry) {
    if (entry->impl) {
        closedir(entry->impl);
        entry->impl = NULL;
    }
}
