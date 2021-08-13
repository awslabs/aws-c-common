/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/file.h>
#include <aws/common/string.h>

#include <aws/testing/aws_test_harness.h>

#include <fcntl.h>

static int s_aws_fopen_test_helper(char *file_path, char *content) {
    char read_result[100];
    AWS_ZERO_ARRAY(read_result);
    FILE *file = aws_fopen(file_path, "w+");
    ASSERT_NOT_NULL(file);
    fprintf(file, "%s", content);
    fclose(file);
    FILE *readfile = aws_fopen(file_path, "r");
    ASSERT_NOT_NULL(readfile);
    size_t read_len = fread(read_result, sizeof(char), strlen(content), readfile);
    ASSERT_UINT_EQUALS(strlen(content), read_len);
    fclose(readfile);
    ASSERT_SUCCESS(strcmp(content, read_result));

#ifdef _WIN32
    wchar_t w_file_path[1000];
    /* plus one for the EOS */
    size_t file_path_len = strlen(file_path) + 1;
    MultiByteToWideChar(CP_UTF8, 0, file_path, -1, w_file_path, (int)file_path_len);
    ASSERT_SUCCESS(_wremove(w_file_path));
#else
    ASSERT_SUCCESS(remove(file_path));
#endif
    return AWS_OP_SUCCESS;
}

static int s_aws_fopen_content_matches(char *file_path, char *content) {
    char read_result[100];
    AWS_ZERO_ARRAY(read_result);
    FILE *file = aws_fopen(file_path, "rb");
    ASSERT_NOT_NULL(file);
    size_t read_len = fread(read_result, sizeof(char), strlen(content), file);
    ASSERT_UINT_EQUALS(strlen(content), read_len);
    fclose(file);
    ASSERT_SUCCESS(strcmp(content, read_result));

    return AWS_OP_SUCCESS;
}

static int s_aws_fopen_non_ascii_read_existing_file_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    char expected_content[] = "This is a non-ascii file path file.";
    char file_path[] = "Å Éxample.txt";
    char read_result[100];
    AWS_ZERO_ARRAY(read_result);
    FILE *readfile = aws_fopen(file_path, "r");
    ASSERT_NOT_NULL(readfile);
    size_t read_len = fread(read_result, sizeof(char), strlen(expected_content), readfile);
    ASSERT_UINT_EQUALS(strlen(expected_content), read_len);
    fclose(readfile);
    ASSERT_SUCCESS(strcmp(expected_content, read_result));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_non_ascii_read_existing_file_test, s_aws_fopen_non_ascii_read_existing_file_test_fn)

static int s_aws_fopen_non_ascii_test_fn(struct aws_allocator *allocator, void *ctx) {

    (void)allocator;
    (void)ctx;
    char file_path[] = "Éxample.txt";
    char content[] = "samples";
    ASSERT_SUCCESS(s_aws_fopen_test_helper(file_path, content));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_non_ascii_test, s_aws_fopen_non_ascii_test_fn)

static int s_aws_fopen_ascii_test_fn(struct aws_allocator *allocator, void *ctx) {

    (void)allocator;
    (void)ctx;
    char file_path[] = "sample.txt";
    char content[] = "samples";
    ASSERT_SUCCESS(s_aws_fopen_test_helper(file_path, content));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_ascii_test, s_aws_fopen_ascii_test_fn)

struct directory_traversal_test_data {
    bool child_dir_verified;
    bool child_file_verified;
    bool root_file_verified;
};

static const char *s_first_child_dir_path = "dir_traversal_test" AWS_PATH_DELIM_STR "first_child_dir";

static const char *s_first_child_file_path =
    "dir_traversal_test" AWS_PATH_DELIM_STR "first_child_dir" AWS_PATH_DELIM_STR "child.txt";

static const char *s_root_child_path = "dir_traversal_test" AWS_PATH_DELIM_STR "root_child.txt";

bool s_on_directory_entry(const struct aws_directory_entry *entry, void *user_data) {
    struct directory_traversal_test_data *test_data = user_data;

    if (aws_byte_cursor_eq_c_str(&entry->relative_path, s_root_child_path)) {
        test_data->root_file_verified =
            entry->file_type & AWS_FILE_TYPE_FILE && entry->file_size &&
            s_aws_fopen_content_matches((char *)entry->relative_path.ptr, "dir_traversal_test->root_child.txt") ==
                AWS_OP_SUCCESS;
        return true;
    }

    if (aws_byte_cursor_eq_c_str(&entry->relative_path, s_first_child_file_path)) {
        test_data->child_file_verified =
            entry->file_type & AWS_FILE_TYPE_FILE && entry->file_size &&
            s_aws_fopen_content_matches(
                (char *)entry->relative_path.ptr, "dir_traversal_test->first_child_dir->child.txt") == AWS_OP_SUCCESS;
        return true;
    }

    if (aws_byte_cursor_eq_c_str(&entry->relative_path, s_first_child_dir_path)) {
        test_data->child_dir_verified = entry->file_type & AWS_FILE_TYPE_DIRECTORY;
        return true;
    }

    return false;
}

static int s_directory_traversal_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "dir_traversal_test");
    struct directory_traversal_test_data test_data;
    AWS_ZERO_STRUCT(test_data);

    ASSERT_SUCCESS(aws_directory_traverse(allocator, path, true, s_on_directory_entry, &test_data));
    ASSERT_TRUE(test_data.child_dir_verified);
    ASSERT_TRUE(test_data.root_file_verified);
    ASSERT_TRUE(test_data.child_file_verified);

    AWS_ZERO_STRUCT(test_data);
    ASSERT_SUCCESS(aws_directory_traverse(allocator, path, false, s_on_directory_entry, &test_data));
    ASSERT_TRUE(test_data.child_dir_verified);
    ASSERT_TRUE(test_data.root_file_verified);
    ASSERT_FALSE(test_data.child_file_verified);

    aws_string_destroy(path);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_traversal_test, s_directory_traversal_test_fn)

struct directory_traversal_abort_test_data {
    int times_called;
};

bool directory_traversal_abort_test_data(const struct aws_directory_entry *entry, void *user_data) {
    struct directory_traversal_abort_test_data *test_data = user_data;
    test_data->times_called += 1;

    return false;
}

static int s_directory_traversal_stop_traversal_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "dir_traversal_test");
    struct directory_traversal_abort_test_data test_data;
    AWS_ZERO_STRUCT(test_data);

    ASSERT_ERROR(
        AWS_ERROR_OPERATION_INTERUPTED,
        aws_directory_traverse(allocator, path, true, directory_traversal_abort_test_data, &test_data));
    ASSERT_INT_EQUALS(1, test_data.times_called);

    aws_string_destroy(path);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_traversal_stop_traversal, s_directory_traversal_stop_traversal_fn)

static int s_directory_traversal_on_file_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "dir_traversal_test/root_child.txt");
    struct directory_traversal_test_data test_data;
    AWS_ZERO_STRUCT(test_data);

    ASSERT_ERROR(
        AWS_ERROR_FILE_INVALID_PATH, aws_directory_traverse(allocator, path, true, s_on_directory_entry, &test_data));

    aws_string_destroy(path);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_traversal_on_file_test, s_directory_traversal_on_file_test_fn)

static int s_directory_existence_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "dir_traversal_test");
    ASSERT_TRUE(aws_directory_exists(path));
    aws_string_destroy(path);

    path = aws_string_new_from_c_str(allocator, "dir_traversal_test_blah");
    ASSERT_FALSE(aws_directory_exists(path));
    aws_string_destroy(path);

    path = aws_string_new_from_c_str(allocator, "dir_traversal_test/root_child.txt");
    ASSERT_FALSE(aws_directory_exists(path));
    aws_string_destroy(path);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_existence_test, s_directory_existence_test_fn)

static int s_directory_creation_deletion_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "temp_dir");
    ASSERT_SUCCESS(aws_directory_create(path));

    /* should be idempotent */
    ASSERT_SUCCESS(aws_directory_create(path));

    ASSERT_TRUE(aws_directory_exists(path));
    ASSERT_SUCCESS(aws_directory_delete(path, allocator, false));
    ASSERT_FALSE(aws_directory_exists(path));

    aws_string_destroy(path);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_creation_deletion_test, s_directory_creation_deletion_test_fn)

static int s_directory_non_empty_deletion_fails_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "dir_traversal_test");
    ASSERT_TRUE(aws_directory_exists(path));
    ASSERT_ERROR(AWS_ERROR_DIRECTORY_NOT_EMPTY, aws_directory_delete(path, allocator, false));
    ASSERT_TRUE(aws_directory_exists(path));

    aws_string_destroy(path);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_non_empty_deletion_fails_test, s_directory_non_empty_deletion_fails_test_fn)

static int s_directory_non_empty_deletion_recursively_succeeds_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "non_empty_dir_del_test_dir_1");
    ASSERT_SUCCESS(aws_directory_create(path));

    const char *nested_dir = "non_empty_dir_del_test_dir_1" AWS_PATH_DELIM_STR "test_dir_2";
    struct aws_string *nested_dir_path = aws_string_new_from_c_str(allocator, nested_dir);
    ASSERT_SUCCESS(aws_directory_create(nested_dir_path));

    const char *nested_file =
        "non_empty_dir_del_test_dir_1" AWS_PATH_DELIM_STR "test_dir_2" AWS_PATH_DELIM_STR "nested_file.txt";

    FILE *nested_file_ptr = aws_fopen(nested_file, "w");
    ASSERT_NOT_NULL(nested_file_ptr);
    fclose(nested_file_ptr);

    ASSERT_SUCCESS(aws_directory_delete(path, allocator, true));
    ASSERT_FALSE(aws_directory_exists(path));

    aws_string_destroy(nested_dir_path);
    aws_string_destroy(path);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(
    directory_non_empty_deletion_recursively_succeeds_test,
    s_directory_non_empty_deletion_recursively_succeeds_test_fn)

static int s_directory_move_succeeds_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "directory_move_succeeds_test_dir_1");
    ASSERT_SUCCESS(aws_directory_create(path));

    struct aws_string *to_path = aws_string_new_from_c_str(allocator, "directory_move_succeeds_test_dir_2");
    ASSERT_SUCCESS(aws_directory_or_file_move(path, to_path));

    ASSERT_FALSE(aws_directory_exists(path));
    ASSERT_TRUE(aws_directory_exists(to_path));

    aws_string_destroy(to_path);
    aws_string_destroy(path);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_move_succeeds_test, s_directory_move_succeeds_test_fn)

static int s_directory_move_src_non_existent_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *path = aws_string_new_from_c_str(allocator, "directory_move_src_non_existent_test_dir_1");

    struct aws_string *to_path = aws_string_new_from_c_str(allocator, "directory_move_src_non_existent_test_dir_2");
    ASSERT_ERROR(AWS_ERROR_FILE_INVALID_PATH, aws_directory_or_file_move(path, to_path));

    aws_string_destroy(to_path);
    aws_string_destroy(path);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_move_src_non_existent_test, s_directory_move_src_non_existent_test_fn)
