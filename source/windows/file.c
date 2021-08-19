/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <aws/common/string.h>
#include <errno.h>
#include <stdio.h>
#include <windows.h>

FILE *aws_fopen_safe(const struct aws_string *file_path, const struct aws_string *mode) {

    struct aws_string *w_file_path = aws_string_convert_to_wchar_str(aws_default_allocator(), file_path);
    struct aws_string *w_mode = aws_string_convert_to_wchar_str(aws_default_allocator(), mode);

    FILE *file = NULL;
    errno_t error = _wfopen_s(&file, aws_string_wchar_c_str(w_file_path), aws_string_wchar_c_str(w_mode));
    /* actually handle the error correctly here. */
    aws_string_destroy(w_mode);
    aws_string_destroy(w_file_path);

    if (error) {
        aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    }

    return file;
}

struct aws_string *s_to_long_path(const struct aws_string *path) {
    wchar_t prefix[] = L"\\\\?\\";

    struct aws_byte_buf new_path;
    aws_byte_buf_init(&new_path, aws_default_allocator(), sizeof(prefix) + path->len + 2);

    struct aws_byte_cursor prefix_cur = aws_byte_cursor_from_array((uint8_t *)prefix, sizeof(prefix));
    aws_byte_buf_append_dynamic(&new_path, &prefix_cur);

    struct aws_byte_cursor path_cur = aws_byte_cursor_from_array(aws_string_bytes(path), path->len);
    aws_byte_buf_append_dynamic(&new_path, &path_cur);

    struct aws_string *long_path = aws_string_new_from_buf(aws_default_allocator(), &new_path);
    aws_byte_buf_clean_up(&new_path);

    return new_path;
}

int aws_directory_create(const struct aws_string *dir_path) {
    struct aws_string *w_dir_path = aws_string_convert_to_wchar_str(aws_default_allocator(), dir_path);
    struct aws_string *long_dir_path = s_to_long_path(w_dir_path);
    aws_string_destroy(w_dir_path);

    int create_dir_res = CreateDirectoryW(aws_string_wchar_c_str(long_dir_path), NULL);
    aws_string_destroy(long_dir_path);

    if (create_dir_res == ERROR_PATH_NOT_FOUND) {
        return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    }

    return AWS_OP_SUCCESS;
}

bool aws_directory_exists(const struct aws_string *dir_path) {
    struct aws_string *w_dir_path = aws_string_convert_to_wchar_str(aws_default_allocator(), dir_path);
    struct aws_string *long_dir_path = s_to_long_path(w_dir_path);
    aws_string_destroy(w_dir_path);

    DWORD attributes = GetFileAttributes(aws_string_wchar_c_str(long_dir_path));
    aws_string_destroy(long_dir_path);

    return (dwAttrib != INVALID_FILE_ATTRIBUTES && (dwAttrib & FILE_ATTRIBUTE_DIRECTORY));
}

static bool s_delete_file_or_directory(const struct aws_directory_entry *entry, void *user_data) {
    (void)user_data;

    struct aws_allocator *allocator = aws_default_allocator();

    struct aws_string *path_str = aws_string_new_from_cursor(allocator, &entry->relative_path);
    int ret_val = AWS_OP_SUCCESS;

    if (entry->file_type & AWS_FILE_TYPE_FILE) {
        ret_val = aws_file_delete(path_str);
    }

    if (entry->file_type & AWS_FILE_TYPE_DIRECTORY) {
        ret_val = aws_directory_delete(path_str, false);
    }

    aws_string_destroy(path_str);
    return ret_val == AWS_OP_SUCCESS;
}

int aws_directory_delete(const struct aws_string *dir_path, bool recursive) {
    if (!aws_directory_exists(dir_path)) {
        return AWS_OP_SUCCESS;
    }

    if (recursive) {
        ret_val = aws_directory_traverse(aws_default_allocator(), dir_path, true, s_delete_file_or_directory, NULL);
    }

    if (ret_val && aws_last_error() == AWS_ERROR_FILE_INVALID_PATH) {
        aws_reset_error();
        return AWS_OP_SUCCESS;
    }

    if (ret_val) {
        return AWS_OP_ERR;
    }

    struct aws_string *w_dir_path = aws_string_convert_to_wchar_str(aws_default_allocator(), dir_path);
    struct aws_string *long_dir_path = s_to_long_path(w_dir_path);
    aws_string_destroy(w_dir_path);

    BOOL remove_dir_res = RemoveDirectoryW(aws_string_wchar_c_str(long_dir_path));
    aws_string_destroy(long_dir_path);

    if (!remove_dir_res) {
        int error = GetLastError();
        if (error == ERROR_DIR_NOT_EMPTY) {
            return aws_raise_error(AWS_ERROR_DIRECTORY_NOT_EMPTY);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    return AWS_OP_SUCCESS;
}

int aws_file_delete(const struct aws_string *file_path) {
    struct aws_string *w_file_path = aws_string_convert_to_wchar_str(aws_default_allocator(), file_path);
    struct aws_string *long_file_path = s_to_long_path(w_file_path);
    aws_string_destroy(w_file_path);

    BOOL remove_file_res = DeleteFileW(aws_string_wchar_c_str(long_file_path));
    aws_string_destroy(long_file_path);

    if (!remove_file_res) {
        int error = GetLastError();
        if (error == ERROR_FILE_NOT_FOUND) {
            return AWS_OP_SUCCESS;
        }

        if (error == ERROR_ACCESS_DENIED) {
            return aws_raise_error(AWS_ERROR_NO_PERMISSION);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    return AWS_OP_SUCCESS;
}

int aws_directory_or_file_move(const struct aws_string *from, const struct aws_string *to) {
    struct aws_string *w_from_path = aws_string_convert_to_wchar_str(aws_default_allocator(), from);
    struct aws_string *long_from_path = s_to_long_path(w_from_path);
    aws_string_destroy(w_from_path);

    struct aws_string *w_to_path = aws_string_convert_to_wchar_str(aws_default_allocator(), to);
    struct aws_string *long_to_path = s_to_long_path(w_to_path);
    aws_string_destroy(w_to_path);

    BOOL move_res = MoveFileW(aws_string_wchar_c_str(long_from_path), aws_string_wchar_c_str(long_to_path));
    aws_string_destroy(long_from_path);
    aws_string_destroy(long_to_path);

    if (!move_res) {
        int error = GetLastError();
        if (error == ERROR_FILE_NOT_FOUND) {
            return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        }

        if (error == ERROR_ACCESS_DENIED) {
            return aws_raise_error(AWS_ERROR_NO_PERMISSION);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    return AWS_OP_SUCCESS;
}

int aws_directory_traverse(
    struct aws_allocator *allocator,
    const struct aws_string *path,
    bool recursive,
    aws_on_directory_entry *on_entry,
    void *user_data) {
    struct aws_string *w_path = aws_string_convert_to_wchar_str(allocator, path);
    struct aws_string *long_path = s_to_long_path(w_path);
    aws_string_destroy(w_path);

    WIN32_FIND_DATAW ffd;
    HANDLE find_handle = FindFirstFileW(aws_string_wchar_c_str(long_path), &ffd);

    if (find_handle == INVALID_HANDLE_VALUE) {
        aws_string_destroy(long_path);

        int error = GetLastError();

        if (error == ERROR_FILE_NOT_FOUND) {
            return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    FindClose(find_handle);
    /* create search path string */
    struct aws_byte_cursor path_cur = aws_byte_cursor_from_array(aws_string_bytes(long_path), long_path->len);
    struct aws_byte_buf search_buf;
    aws_byte_buf_init_copy_from_cursor(&search_buf, allocator, &path_cur);
    aws_string_destroy(long_path);
    wchar_t search_wchar_pattern[] = L"\\*";
    struct aws_byte_cursor search_char =
        aws_byte_cursor_from_array((uint8_t *)search_wchar_pattern, sizeof(search_wchar_pattern));

    aws_byte_buf_append_dynamic(&search_buf, &search_char);
    /* it's already converted to wide string */
    struct aws_string *search_string = aws_string_new_from_buf(allocator, &search_buf);
    search_buf.len -= sizeof(search_wchar_pattern);

    find_handle = FindFirstFileW(aws_string_wchar_c_str(search_string), &ffd);
    aws_string_destroy(search_string);
    aws_byte_buf_clean_up(&search_buf);

    int ret_val = AWS_OP_SUCCESS;

    while (ret_val == AWS_OP_SUCCESS) {
        struct aws_string *name_component_str = aws_string_convert_from_wchar_c_str(ffd.cFileName);
        struct aws_byte_cursor name_component = aws_byte_cursor_from_string(name_component_str);

        if (aws_byte_cursor_eq_c_str(&name_component, "..") || aws_byte_cursor_eq_c_str(&name_component, ".")) {
            aws_string_destroy(name_component_str);
            continue;
        }

        struct aws_byte_buf relative_path;
        aws_byte_buf_init_copy_from_cursor(&relative_path, allocator, current_path);
        aws_byte_buf_append_byte_dynamic(&relative_path, AWS_PATH_DELIM);
        aws_byte_buf_append_dynamic(&relative_path, &name_component);
        aws_byte_buf_append_byte_dynamic(&relative_path, 0);
        relative_path.len -= 1;

        struct aws_byte_cursor relative_path_cur = aws_byte_cursor_from_buf(&relative_path);
        struct aws_string *wchar_short_name =
            aws_string_convert_to_wchar_from_byte_cursor(allocator, &relative_path_cur);
        DWORD path_res = GetFullPathNameW(aws_string_wchar_c_str(wchar_short_name), 0, NULL, NULL);

        AWS_FATAL_ASSERT(path_res > 0);
        struct aws_byte_buf full_path_buf;
        aws_byte_buf_init(&full_path_buf, allocator, (size_t)path_res * sizeof(wchar_t) + 2);

        full_path_buf.len = path_res + 1;
        path_res = GetFullPathNameW(
            aws_string_wchar_c_str(wchar_short_name), (DWORD)wchar_short_name->len, full_path_buf.buffer, NULL);
        AWS_FATAL_ASSERT(path_res > 0);
        aws_string_destroy(wchar_short_name);

        struct aws_string *full_path_name_converted =
            aws_string_convert_from_wchar_c_str(allocator, (wchar_t *)full_path_buf.buffer);
        aws_byte_buf_clean_up(&full_path_buf);

        struct aws_directory_entry entry;
        AWS_ZERO_STRUCT(entry);
        entry.relative_path = relative_path_cur;
        entry.path = aws_byte_cursor_from_string(full_path_name_converted);

        LARGE_INTEGER file_size;
        file_size.HighPart = ffd.nFileSizeHigh;
        file_size.LowPart = ffd.nFileSizeLow;
        entry.file_size = (int64_t)file_size.QuadPart;

        if (ffd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) {
            entry.file_type |= AWS_FILE_TYPE_DIRECTORY;
        } else {
            entry.file_type |= AWS_FILE_TYPE_FILE;
        }

        if (recursive && entry.file_type & AWS_FILE_TYPE_DIRECTORY) {
            struct aws_string *rel_path_str = aws_string_new_from_cursor(allocator, &entry.relative_path);
            ret_val = aws_directory_traverse(allocator, rel_path_str, recursive, on_entry, user_data);
            aws_string_destroy(rel_path_str);
        }

        /* post order traversal, if a node below us ended the traversal, don't call the visitor again. */
        if (ret_val && aws_last_error() == AWS_ERROR_OPERATION_INTERUPTED) {
            goto cleanup;
        }

        if (!on_entry(&entry, user_data)) {
            ret_val = aws_raise_error(AWS_ERROR_OPERATION_INTERUPTED);
            goto cleanup;
        }

        if (ret_val) {
            goto cleanup;
        }

    cleanup:
        aws_string_destroy(full_path_name_converted);
        aws_byte_buf_clean_up(&relative_path);

        if (!FindNextFileW(find_handle, &ffd)) {
            break;
        }
    }

    if (find_handle != INVALID_HANDLE_VALUE) {
        FindClose(find_handle);
    }
    return ret_val;
}
