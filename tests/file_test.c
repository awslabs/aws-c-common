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

static int s_directory_traversal_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_byte_cursor path = aws_byte_cursor_from_c_str("dir_traversal_test");

    struct aws_directory_entry *root = aws_directory_entry_open(allocator, path, path);
    ASSERT_NOT_NULL(root);
    ASSERT_INT_EQUALS(AWS_FILE_TYPE_DIRECTORY, root->file_type);

    struct aws_directory_entry *first_child = aws_directory_entry_descend(root);
    ASSERT_NOT_NULL(first_child);

    struct aws_directory_entry *child_txt = NULL;
    /* this stuff isn't deterministic order wise so we gotta handle both orders. */
    if (first_child->file_type == AWS_FILE_TYPE_FILE) {
        ASSERT_SUCCESS(s_aws_fopen_test_helper(
            (char *)aws_string_c_str(first_child->relative_path), "dir_traversal_test->root_child.txt"));

        struct aws_directory_entry *next_child = aws_directory_entry_get_next_sibling(first_child);
        ASSERT_NOT_NULL(next_child);
        ASSERT_INT_EQUALS(AWS_FILE_TYPE_DIRECTORY, next_child->file_type);

        child_txt = aws_directory_entry_descend(next_child);
    } else {
        child_txt = aws_directory_entry_descend(first_child);

        struct aws_directory_entry *next_child = aws_directory_entry_get_next_sibling(first_child);
        ASSERT_NOT_NULL(next_child);
        ASSERT_INT_EQUALS(AWS_FILE_TYPE_FILE, next_child->file_type);
        ASSERT_SUCCESS(s_aws_fopen_test_helper(
            (char *)aws_string_c_str(next_child->relative_path), "dir_traversal_test->root_child.txt"));
    }

    ASSERT_NOT_NULL(child_txt);
    ASSERT_INT_EQUALS(AWS_FILE_TYPE_FILE, child_txt->file_type);
    ASSERT_SUCCESS(s_aws_fopen_test_helper((char *)aws_string_c_str(child_txt->relative_path),
                                           "dir_traversal_test->first_child_dir->child.txt"));


    aws_directory_entry_release(root);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(directory_traversal_test, s_directory_traversal_test_fn)
