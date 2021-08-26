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

struct aws_string *s_to_long_path(struct aws_allocator *allocator, const struct aws_string *path) {

    wchar_t prefix[] = L"\\\\?\\";
    size_t prefix_size = sizeof(prefix);
    if (path->len > MAX_PATH - prefix_size) {

        struct aws_byte_buf new_path;
        aws_byte_buf_init(&new_path, allocator, sizeof(prefix) + path->len + 2);

        struct aws_byte_cursor prefix_cur = aws_byte_cursor_from_array((uint8_t *)prefix, sizeof(prefix) - 2);
        aws_byte_buf_append_dynamic(&new_path, &prefix_cur);

        struct aws_byte_cursor path_cur = aws_byte_cursor_from_array(aws_string_bytes(path), path->len);
        aws_byte_buf_append_dynamic(&new_path, &path_cur);

        struct aws_string *long_path = aws_string_new_from_buf(allocator, &new_path);
        aws_byte_buf_clean_up(&new_path);

        return long_path;
    }

    return aws_string_new_from_string(allocator, path);
}

int aws_directory_create(const struct aws_string *dir_path) {
    struct aws_string *w_dir_path = aws_string_convert_to_wchar_str(aws_default_allocator(), dir_path);
    struct aws_string *long_dir_path = s_to_long_path(aws_default_allocator() , w_dir_path);
    aws_string_destroy(w_dir_path);

    BOOL create_dir_res = CreateDirectoryW(aws_string_wchar_c_str(long_dir_path), NULL);
    aws_string_destroy(long_dir_path);

    int error = GetLastError();
    if (!create_dir_res) {
        if (error == ERROR_ALREADY_EXISTS) {
            return AWS_OP_SUCCESS;
        }

        if (error == ERROR_PATH_NOT_FOUND) {
            return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        }

        if (error == ERROR_ACCESS_DENIED) {
            return aws_raise_error(AWS_ERROR_NO_PERMISSION);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    return AWS_OP_SUCCESS;
}

bool aws_directory_exists(const struct aws_string *dir_path) {
    struct aws_string *w_dir_path = aws_string_convert_to_wchar_str(aws_default_allocator(), dir_path);
    struct aws_string *long_dir_path = s_to_long_path(aws_default_allocator(), w_dir_path);
    aws_string_destroy(w_dir_path);

    DWORD attributes = GetFileAttributesW(aws_string_wchar_c_str(long_dir_path));
    aws_string_destroy(long_dir_path);

    return (attributes != INVALID_FILE_ATTRIBUTES && (attributes & FILE_ATTRIBUTE_DIRECTORY));
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

    int ret_val = AWS_OP_SUCCESS;

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
    struct aws_string *long_dir_path = s_to_long_path(aws_default_allocator(), w_dir_path);
    aws_string_destroy(w_dir_path);

    BOOL remove_dir_res = RemoveDirectoryW(aws_string_wchar_c_str(long_dir_path));
    aws_string_destroy(long_dir_path);

    if (!remove_dir_res) {
        int error = GetLastError();
        if (error == ERROR_DIR_NOT_EMPTY) {
            return aws_raise_error(AWS_ERROR_DIRECTORY_NOT_EMPTY);
        }

        if (error == ERROR_ACCESS_DENIED) {
            return aws_raise_error(AWS_ERROR_NO_PERMISSION);
        }
        
        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    return AWS_OP_SUCCESS;
}

int aws_file_delete(const struct aws_string *file_path) {
    struct aws_string *w_file_path = aws_string_convert_to_wchar_str(aws_default_allocator(), file_path);
    struct aws_string *long_file_path = s_to_long_path(aws_default_allocator(), w_file_path);
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
    struct aws_string *long_from_path = s_to_long_path(aws_default_allocator(), w_from_path);
    aws_string_destroy(w_from_path);

    struct aws_string *w_to_path = aws_string_convert_to_wchar_str(aws_default_allocator(), to);
    struct aws_string *long_to_path = s_to_long_path(aws_default_allocator(), w_to_path);
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
    struct aws_string *w_path_wchar = aws_string_convert_to_wchar_str(allocator, path);
    struct aws_string *long_path_wchar = s_to_long_path(allocator, w_path_wchar);
    aws_string_destroy(w_path_wchar);

    /* windows doesn't fail in FindFirstFile if it's not a directory. Do the check here. We don't call the perfectly
       good function for this check because the string is already converted to utf-16 and it's trivial to reuse it. */
    DWORD attributes = GetFileAttributesW(aws_string_wchar_c_str(long_path_wchar));
    if (!(attributes & FILE_ATTRIBUTE_DIRECTORY)) {
        aws_string_destroy(long_path_wchar);
        return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
    }

    WIN32_FIND_DATAW ffd;
    HANDLE find_handle = FindFirstFileW(aws_string_wchar_c_str(long_path_wchar), &ffd);

    if (find_handle == INVALID_HANDLE_VALUE) {
        aws_string_destroy(long_path_wchar);

        int error = GetLastError();

        if (error == ERROR_FILE_NOT_FOUND) {
            return aws_raise_error(AWS_ERROR_FILE_INVALID_PATH);
        }

        return aws_raise_error(AWS_ERROR_UNKNOWN);
    }

    FindClose(find_handle);

    /* create search path string */
    struct aws_byte_cursor path_wchar_cur =
        aws_byte_cursor_from_array(aws_string_bytes(long_path_wchar), long_path_wchar->len);
    struct aws_byte_buf search_wchar_buf;
    aws_byte_buf_init_copy_from_cursor(&search_wchar_buf, allocator, path_wchar_cur);

    wchar_t search_wchar_pattern[] = L"\\*";
    struct aws_byte_cursor search_char_wchar =
        aws_byte_cursor_from_array((uint8_t *)search_wchar_pattern, sizeof(search_wchar_pattern));

    aws_byte_buf_append_dynamic(&search_wchar_buf, &search_char_wchar);
    /* it's already converted to wide string */
    struct aws_string *search_wchar_string = aws_string_new_from_buf(allocator, &search_wchar_buf);

    find_handle = FindFirstFileW(aws_string_wchar_c_str(search_wchar_string), &ffd);
    aws_string_destroy(search_wchar_string);
    aws_byte_buf_clean_up(&search_wchar_buf);

    int ret_val = AWS_OP_SUCCESS;

    /* iterate each entry in the directory. Do a bunch of utf-16 conversions. Figure out the paths etc....
       invoke the visitor, and continue recursing if the flag was set. */
    do {
        struct aws_string *name_component_multi_char_str =
            aws_string_convert_from_wchar_c_str(allocator, ffd.cFileName);
        struct aws_byte_cursor name_component_multi_char = aws_byte_cursor_from_string(name_component_multi_char_str);

        /* disgard . and .. */
        char *ascend_mark = "..";
        char *cd_mark = ".";
        struct aws_byte_cursor ascend_mark_cur = aws_byte_cursor_from_c_str(ascend_mark);
        struct aws_byte_cursor cd_mark_cur = aws_byte_cursor_from_c_str(cd_mark);
        if (aws_byte_cursor_eq(&name_component_multi_char, &ascend_mark_cur) ||
            aws_byte_cursor_eq(&name_component_multi_char, &cd_mark_cur)) {
            aws_string_destroy(name_component_multi_char_str);
            continue;
        }

        /* get the relative path as utf-16, so we can talk to windows. */
        struct aws_byte_buf relative_path_wchar;
        aws_byte_buf_init_copy_from_cursor(&relative_path_wchar, allocator, path_wchar_cur);

        wchar_t unicode_delim[] = L"\\";
        struct aws_byte_cursor delimiter_cur =
            aws_byte_cursor_from_array((uint8_t *)unicode_delim, sizeof(unicode_delim) - 2);
        aws_byte_buf_append_dynamic(&relative_path_wchar, &delimiter_cur);
        struct aws_byte_cursor name_str =
            aws_byte_cursor_from_array(ffd.cFileName, wcsnlen(ffd.cFileName, sizeof(ffd.cFileName)) * sizeof(wchar_t));
        aws_byte_buf_append_dynamic(&relative_path_wchar, &name_str);
        aws_byte_buf_append_byte_dynamic(&relative_path_wchar, 0);
        aws_byte_buf_append_byte_dynamic(&relative_path_wchar, 0);

        relative_path_wchar.len -= 2;

        /* now get the absolute path from the relative path we just computed. */
        DWORD path_res = GetFullPathNameW((wchar_t *)relative_path_wchar.buffer, 0, NULL, NULL);

        AWS_FATAL_ASSERT(path_res > 0);
        struct aws_byte_buf full_path_wchar_buf;
        aws_byte_buf_init(&full_path_wchar_buf, allocator, (size_t)path_res * sizeof(wchar_t) + 2);

        full_path_wchar_buf.len = full_path_wchar_buf.capacity - 2;
        path_res = GetFullPathNameW(
            (wchar_t *)relative_path_wchar.buffer, (DWORD)path_res + 1, (wchar_t *)full_path_wchar_buf.buffer, NULL);
        AWS_FATAL_ASSERT(path_res > 0);

        aws_byte_buf_append_byte_dynamic(&full_path_wchar_buf, 0);
        aws_byte_buf_append_byte_dynamic(&full_path_wchar_buf, 0);

        /* now we have the data, convert the utf-16 strings we used to communicate with windows back to
           utf-8 for the user to actually consume. */
        struct aws_string *full_path_name_multi_char =
            aws_string_convert_from_wchar_c_str(allocator, (wchar_t *)full_path_wchar_buf.buffer);
        aws_byte_buf_clean_up(&full_path_wchar_buf);

        struct aws_string *relative_path_multi_char =
            aws_string_convert_from_wchar_c_str(allocator, (wchar_t *)relative_path_wchar.buffer);


        struct aws_directory_entry entry;
        AWS_ZERO_STRUCT(entry);
        entry.relative_path = aws_byte_cursor_from_string(relative_path_multi_char);
        entry.path = aws_byte_cursor_from_string(full_path_name_multi_char);

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
            ret_val = aws_directory_traverse(allocator, relative_path_multi_char, recursive, on_entry, user_data);
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
        aws_string_destroy(relative_path_multi_char);
        aws_string_destroy(full_path_name_multi_char);
        aws_byte_buf_clean_up(&relative_path_wchar);
        aws_string_destroy(name_component_multi_char_str);

    } while (ret_val == AWS_OP_SUCCESS && FindNextFileW(find_handle, &ffd));

    aws_string_destroy(long_path_wchar);
    if (find_handle != INVALID_HANDLE_VALUE) {
        FindClose(find_handle);
    }

    return ret_val;
}
