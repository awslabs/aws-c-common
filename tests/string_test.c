/*
* Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
*
* Licensed under the Apache License, Version 2.0 (the "License").
* You may not use this file except in compliance with the License.
* A copy of the License is located at
*
*  http://aws.amazon.com/apache2.0
*
* or in the "license" file accompanying this file. This file is distributed
* on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
* express or implied. See the License for the specific language governing
* permissions and limitations under the License.
*/

#include <aws/testing/aws_test_harness.h>
#include <aws/common/byte_buf.h>

static int test_char_split_happy_path_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(3, aws_array_list_length(&output), "Split should have returned %d elements", 3);

    struct aws_byte_buf value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0), "Retrieving element at 0 failed.");

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 0 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1), "Retrieving element at 1 failed.");
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 1 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2), "Retrieving element at 2 failed.");
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 2 should have been %s", expected);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_happy_path, test_char_split_happy_path_fn)

static int test_char_split_ends_with_token_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;testb;testc;";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(3, aws_array_list_length(&output), "Split should have returned %d elements", 3);

    struct aws_byte_buf value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0), "Retrieving element at 0 failed.");

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 0 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1), "Retrieving element at 1 failed.");
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 1 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2), "Retrieving element at 2 failed.");
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 2 should have been %s", expected);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_ends_with_token, test_char_split_ends_with_token_fn)

static int test_char_split_begins_with_token_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = ";testa;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(4, aws_array_list_length(&output), "Split should have returned %d elements", 3);

    struct aws_byte_buf value = {0};

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0), "Retrieving element at 0 failed.");
    char *expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 0 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1), "Retrieving element at 1 failed.");
    expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 1 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2), "Retrieving element at 2 failed.");
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 2 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 3), "Retrieving element at 3 failed.");
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 3 should have been %s", expected);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_begins_with_token, test_char_split_begins_with_token_fn)

static int test_char_split_token_not_present_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(1, aws_array_list_length(&output), "Split should have returned %d elements", 1);

    struct aws_byte_buf value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0), "Retrieving element at 0 failed.");

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 0 should have been %s", expected);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_token_not_present, test_char_split_token_not_present_fn)

static int test_char_split_empty_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(0, aws_array_list_length(&output), "Split should have returned %d elements", 0);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_empty, test_char_split_empty_fn)

static int test_char_split_adj_tokens_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_buf)), "Array list init failed!");
    ASSERT_SUCCESS(aws_string_split_on_char(&to_split, ';', &output), "String split failed");
    ASSERT_INT_EQUALS(4, aws_array_list_length(&output), "Split should have returned %d elements", 4);

    struct aws_byte_buf value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0), "Retrieving element at 0 failed.");

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 0 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1), "Retrieving element at 1 failed.");
    expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 1 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2), "Retrieving element at 2 failed.");
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 2 should have been %s", expected);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 3), "Retrieving element at 3 failed.");
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.buffer,  value.len, "Value 3 should have been %s", expected);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_adj_tokens, test_char_split_adj_tokens_fn)
