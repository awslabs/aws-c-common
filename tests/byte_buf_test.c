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

AWS_TEST_CASE(test_buffer_cat, s_test_buffer_cat_fn)
static int s_test_buffer_cat_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf str1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_c_str(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_c_str(";testc");

    const char expected[] = "testa;testb;testc";

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, str1.len + str2.len + str3.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    ASSERT_INT_EQUALS(strlen(expected), destination.len);
    ASSERT_INT_EQUALS(strlen(expected) + 10, destination.capacity);
    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), destination.buffer, destination.len);

    destination.len = 0;
    ASSERT_SUCCESS(aws_byte_buf_cat(&destination, 1, &str1));
    ASSERT_INT_EQUALS(str1.len, destination.len);
    ASSERT_BIN_ARRAYS_EQUALS(str1.buffer, str1.len, destination.buffer, destination.len);

    destination.len = 0;
    ASSERT_SUCCESS(aws_byte_buf_cat(&destination, 0));
    ASSERT_INT_EQUALS(0, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cat_dest_too_small, s_test_buffer_cat_dest_too_small_fn)
static int s_test_buffer_cat_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf str1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf str2 = aws_byte_buf_from_c_str(";testb");
    struct aws_byte_buf str3 = aws_byte_buf_from_c_str(";testc");

    struct aws_byte_buf destination;
    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, str1.len + str2.len));
    ASSERT_INT_EQUALS(0, destination.len);
    ASSERT_INT_EQUALS(str1.len + str2.len, destination.capacity);

    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_cat(&destination, 3, &str1, &str2, &str3));

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy, s_test_buffer_cpy_fn)
static int s_test_buffer_cpy_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, from.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_append(&destination, &from));

    ASSERT_INT_EQUALS(from.len, destination.len);
    ASSERT_INT_EQUALS(from.len + 10, destination.capacity);

    ASSERT_BIN_ARRAYS_EQUALS(from.ptr, from.len, destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_offsets, s_test_buffer_cpy_offsets_fn)
static int s_test_buffer_cpy_offsets_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    aws_byte_cursor_advance(&from, 2);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, from_buf.len + 10));
    ASSERT_SUCCESS(aws_byte_buf_append(&destination, &from));

    ASSERT_INT_EQUALS(from_buf.len - 2, destination.len);
    ASSERT_INT_EQUALS(from_buf.len + 10, destination.capacity);

    char expected[] = "sta";

    ASSERT_BIN_ARRAYS_EQUALS(expected, strlen(expected), destination.buffer, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_dest_too_small, s_test_buffer_cpy_dest_too_small_fn)
static int s_test_buffer_cpy_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);

    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, from.len - 1));
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(0, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_cpy_offsets_dest_too_small, s_test_buffer_cpy_offsets_dest_too_small_fn)
static int s_test_buffer_cpy_offsets_dest_too_small_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf from_buf = aws_byte_buf_from_c_str("testa");
    struct aws_byte_cursor from = aws_byte_cursor_from_buf(&from_buf);
    struct aws_byte_buf destination;

    ASSERT_SUCCESS(aws_byte_buf_init(&destination, allocator, from.len));
    destination.len = 1;
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append(&destination, &from));
    ASSERT_INT_EQUALS(1, destination.len);

    aws_byte_buf_clean_up(&destination);

    return 0;
}

AWS_TEST_CASE(test_buffer_eq, s_test_buffer_eq_fn)
static int s_test_buffer_eq_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf b1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf b1_equal = aws_byte_buf_from_c_str("testa");

    struct aws_byte_buf b2 = aws_byte_buf_from_c_str("testb");

    b1.capacity = 5;
    b1_equal.capacity = 2;
    b1_equal.allocator = allocator;

    ASSERT_TRUE(aws_byte_buf_eq(&b1, &b1_equal));
    ASSERT_TRUE(aws_byte_buf_eq(&b1, &b1));

    ASSERT_FALSE(aws_byte_buf_eq(&b1, &b2));
    return 0;
}

AWS_TEST_CASE(test_buffer_eq_same_content_different_len, s_test_buffer_eq_same_content_different_len_fn)
static int s_test_buffer_eq_same_content_different_len_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_byte_buf b1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf b2 = aws_byte_buf_from_c_str("testa");
    b2.len--;

    ASSERT_FALSE(aws_byte_buf_eq(&b1, &b2));

    return 0;
}

AWS_TEST_CASE(test_buffer_eq_null_byte_buffer, s_test_buffer_eq_null_byte_buffer_fn)
static int s_test_buffer_eq_null_byte_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_byte_buf b1 = aws_byte_buf_from_c_str("testa");

    ASSERT_TRUE(aws_byte_buf_eq(NULL, NULL));
    ASSERT_FALSE(aws_byte_buf_eq(&b1, NULL));
    ASSERT_FALSE(aws_byte_buf_eq(NULL, &b1));

    return 0;
}

AWS_TEST_CASE(test_buffer_eq_null_internal_byte_buffer, s_test_buffer_eq_null_internal_byte_buffer_fn)
static int s_test_buffer_eq_null_internal_byte_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_byte_buf b1 = aws_byte_buf_from_c_str("testa");
    struct aws_byte_buf b2 = aws_byte_buf_from_c_str("testa");

    b1.buffer = NULL;
    ASSERT_FALSE(aws_byte_buf_eq(&b1, &b2));
    ASSERT_FALSE(aws_byte_buf_eq(&b2, &b1));

    b2.buffer = NULL;
    ASSERT_TRUE(aws_byte_buf_eq(&b1, &b2));

    b2.len++;
    ASSERT_FALSE(aws_byte_buf_eq(&b1, &b2));
    return 0;
}

AWS_TEST_CASE(test_buffer_init_copy, s_test_buffer_init_copy_fn)
static int s_test_buffer_init_copy_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf src = aws_byte_buf_from_c_str("test_string");
    struct aws_byte_buf dest;

    ASSERT_SUCCESS(aws_byte_buf_init_copy(&dest, allocator, &src));
    ASSERT_TRUE(aws_byte_buf_eq(&src, &dest));
    ASSERT_INT_EQUALS(src.len, dest.capacity);
    ASSERT_PTR_EQUALS(allocator, dest.allocator);
    aws_byte_buf_clean_up(&dest);
    return 0;
}

AWS_TEST_CASE(test_buffer_init_copy_null_buffer, s_test_buffer_init_copy_null_buffer_fn)
static int s_test_buffer_init_copy_null_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_buf src;
    src.buffer = NULL;
    src.len = 5;

    struct aws_byte_buf dest;
    ASSERT_SUCCESS(aws_byte_buf_init_copy(&dest, allocator, &src));
    ASSERT_PTR_EQUALS(0, dest.allocator);
    ASSERT_INT_EQUALS(0, dest.capacity);
    ASSERT_INT_EQUALS(0, dest.len);
    ASSERT_PTR_EQUALS(0, dest.buffer);
    aws_byte_buf_clean_up(&dest);
    return 0;
}

AWS_TEST_CASE(test_buffer_advance, s_test_buffer_advance)
static int s_test_buffer_advance(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;

    uint8_t arr[16];
    struct aws_byte_buf src_buf = aws_byte_buf_from_array(arr, sizeof(arr));

    struct aws_byte_buf dst_buf;

    src_buf.len = 0;
    ASSERT_TRUE(aws_byte_buf_advance(&src_buf, &dst_buf, 4));
    ASSERT_NULL(dst_buf.allocator);
    ASSERT_INT_EQUALS(src_buf.len, 4);
    ASSERT_INT_EQUALS(dst_buf.len, 0);
    ASSERT_INT_EQUALS(dst_buf.capacity, 4);
    ASSERT_PTR_EQUALS(src_buf.buffer, arr);
    ASSERT_PTR_EQUALS(dst_buf.buffer, arr);

    ASSERT_TRUE(aws_byte_buf_advance(&src_buf, &dst_buf, 12));
    ASSERT_PTR_EQUALS(dst_buf.buffer, arr + 4);
    ASSERT_INT_EQUALS(src_buf.len, 16);

    src_buf.len = 12;
    ASSERT_FALSE(aws_byte_buf_advance(&src_buf, &dst_buf, 5));
    ASSERT_PTR_EQUALS(dst_buf.buffer, NULL);
    ASSERT_NULL(dst_buf.allocator);
    ASSERT_INT_EQUALS(dst_buf.len, 0);
    ASSERT_INT_EQUALS(dst_buf.capacity, 0);
    ASSERT_INT_EQUALS(src_buf.len, 12);

    return 0;
}