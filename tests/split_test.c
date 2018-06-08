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
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(3, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_happy_path, test_char_split_happy_path_fn)

static int test_char_split_ends_with_token_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;testb;testc;";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(4, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));
    char *expected = "testa";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 3));
    expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_ends_with_token, test_char_split_ends_with_token_fn)

static int test_char_split_begins_with_token_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = ";testa;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(4, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));
    char *expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 3));
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_begins_with_token, test_char_split_begins_with_token_fn)

static int test_char_split_token_not_present_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(1, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_token_not_present, test_char_split_token_not_present_fn)

static int test_char_split_empty_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(1, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));
    ASSERT_INT_EQUALS(0, value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_empty, test_char_split_empty_fn)

static int test_char_split_adj_tokens_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(4, aws_array_list_length(&output));

    struct aws_byte_cursor value = {0};
    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));

    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 3));
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr,  value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_adj_tokens, test_char_split_adj_tokens_fn)

static int test_char_split_with_max_splits_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = ";testa;testb;testc";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&output, allocator, 4, sizeof(struct aws_byte_cursor)));
    ASSERT_SUCCESS(aws_byte_buf_split_on_char_n(&to_split, ';', &output, 2));
    ASSERT_INT_EQUALS(3, aws_array_list_length(&output));

    struct aws_byte_cursor value = { 0 };

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));
    char *expected = "";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testb;testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    aws_array_list_clean_up(&output);

    return 0;
}

AWS_TEST_CASE(test_char_split_with_max_splits, test_char_split_with_max_splits_fn)

static int test_char_split_output_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    const char str_to_split[] = "testa;testb;testc;";

    struct aws_byte_buf to_split = aws_byte_buf_from_literal(str_to_split);

    struct aws_array_list output;
    struct aws_byte_buf output_array[3] = {{0}};
    ASSERT_SUCCESS(aws_array_list_init_static(&output, output_array, 3, sizeof(struct aws_byte_cursor)));
    ASSERT_ERROR(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE, aws_byte_buf_split_on_char(&to_split, ';', &output));
    ASSERT_INT_EQUALS(3, aws_array_list_length(&output));

    struct aws_byte_cursor value = { 0 };

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 0));
    char *expected = "testa";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 1));
    expected = "testb";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    ASSERT_SUCCESS(aws_array_list_get_at(&output, &value, 2));
    expected = "testc";
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), value.ptr, value.len);

    return 0;
}

AWS_TEST_CASE(test_char_split_output_too_small, test_char_split_output_too_small_fn)

static int test_buffer_cat_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf str1 = aws_byte_buf_from_literal("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_literal(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_literal(";testc");


    const char expected[] = "testa;testb;testc";

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, str1.len + str2.len + str3.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    ASSERT_INT_EQUALS(strlen(expected),destination.len);
    ASSERT_INT_EQUALS(strlen(expected) + 10, destination.capacity);
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cat, test_buffer_cat_fn)

static int test_buffer_cat_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf str1 = aws_byte_buf_from_literal("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_literal(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_literal(";testc");

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, str1.len + str2.len));
    ASSERT_INT_EQUALS(0, destination.len);
    ASSERT_INT_EQUALS(str1.len + str2.len, destination.capacity);

    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cat_dest_too_small, test_buffer_cat_dest_too_small_fn)

static int test_buffer_cpy_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf from_buf = aws_byte_buf_from_literal("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_append(&destination, &from));

    ASSERT_INT_EQUALS(from.len, destination.len);
    ASSERT_INT_EQUALS(from.len + 10, destination.capacity);

    ASSERT_BIN_ARRAYS_EQUALS(from.ptr, from.len, destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy, test_buffer_cpy_fn)

static int test_buffer_cpy_offsets_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf from_buf = aws_byte_buf_from_literal("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    aws_byte_cursor_advance(&from, 2);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from_buf.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_append(&destination, &from));

    ASSERT_INT_EQUALS(from_buf.len - 2, destination.len);
    ASSERT_INT_EQUALS(from_buf.len + 10, destination.capacity);

    char expected[] = "sta";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_offsets, test_buffer_cpy_offsets_fn)

static int test_buffer_cpy_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf from_buf = aws_byte_buf_from_literal("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);

    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from.len - 1));
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(0, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_dest_too_small, test_buffer_cpy_dest_too_small_fn)

static int test_buffer_cpy_offsets_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    struct aws_byte_buf from_buf = aws_byte_buf_from_literal("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from.len));
    destination.len = 1;
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(1, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_offsets_dest_too_small, test_buffer_cpy_offsets_dest_too_small_fn)
