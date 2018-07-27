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

#include <aws/common/byte_buf.h>

#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(test_buffer_cat, test_buffer_cat_fn)
static int test_buffer_cat_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf str1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_c_str(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_c_str(";testc");

    const char expected[] = "testa;testb;testc";

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, str1.len + str2.len + str3.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    ASSERT_INT_EQUALS(strlen(expected), destination.len);
    ASSERT_INT_EQUALS(strlen(expected) + 10, destination.capacity);
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cat_dest_too_small, test_buffer_cat_dest_too_small_fn)
static int test_buffer_cat_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf str1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_c_str(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_c_str(";testc");

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, str1.len + str2.len));
    ASSERT_INT_EQUALS(0, destination.len);
    ASSERT_INT_EQUALS(str1.len + str2.len, destination.capacity);

    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy, test_buffer_cpy_fn)
static int test_buffer_cpy_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
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

AWS_TEST_CASE(test_buffer_cpy_offsets, test_buffer_cpy_offsets_fn)
static int test_buffer_cpy_offsets_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
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

AWS_TEST_CASE(test_buffer_cpy_dest_too_small, test_buffer_cpy_dest_too_small_fn)
static int test_buffer_cpy_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);

    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from.len - 1));
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(0, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_offsets_dest_too_small, test_buffer_cpy_offsets_dest_too_small_fn)
static int test_buffer_cpy_offsets_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(allocator, &destination, from.len));
    destination.len = 1;
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(1, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}
