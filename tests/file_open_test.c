/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include "fcntl.h"
#include <aws/common/file_open.h>

#include <aws/testing/aws_test_harness.h>

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
    ASSERT_SUCCESS(remove(file_path));
    return AWS_OP_SUCCESS;
}

static int s_aws_fopen_non_ascii_test_fn(struct aws_allocator *allocator, void *ctx) {

    (void)allocator;
    (void)ctx;
    char file_path[] = "Åsample.txt";
    char content[] = "samples";
    ASSERT_SUCCESS(s_aws_fopen_test_helper(file_path, content));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_non_ascii_test, s_aws_fopen_non_ascii_test_fn)

static int s_aws_fopen_ascii_test_fn(struct aws_allocator *allocator, void *ctx) {

    (void)allocator;
    (void)ctx;
    char file_path[] = "a sample.txt";
    char content[] = "samples";
    ASSERT_SUCCESS(s_aws_fopen_test_helper(file_path, content));
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(aws_fopen_ascii_test, s_aws_fopen_ascii_test_fn)
