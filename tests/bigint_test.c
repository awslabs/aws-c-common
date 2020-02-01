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
#include <aws/common/bigint.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_bigint_from_uint64(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_byte_buf buffer;
    aws_byte_buf_init(&buffer, allocator, 1);

    struct aws_bigint test;

    /* 0 */
    aws_bigint_init_from_uint64(&test, allocator, 0);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 1);
    ASSERT_BIN_ARRAYS_EQUALS("0", 1, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* 1 */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, 1);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 1);
    ASSERT_BIN_ARRAYS_EQUALS("1", 1, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* 128 */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, 128);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 2);
    ASSERT_BIN_ARRAYS_EQUALS("80", 2, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* 255 */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, 255);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 2);
    ASSERT_BIN_ARRAYS_EQUALS("ff", 2, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* UINT32_MAX */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, UINT32_MAX);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 8);
    ASSERT_BIN_ARRAYS_EQUALS("ffffffff", 8, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* UINT32_MAX + 1 */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, (uint64_t)(UINT32_MAX) + 1);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 9);
    ASSERT_BIN_ARRAYS_EQUALS("100000000", 9, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* UINT64_MAX */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, UINT64_MAX);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 16);
    ASSERT_BIN_ARRAYS_EQUALS("ffffffffffffffff", 16, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    /* fedcba9876543210 */
    buffer.len = 0;
    aws_bigint_init_from_uint64(&test, allocator, 18364758544493064720ULL);
    ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
    ASSERT_TRUE(buffer.len == 16);
    ASSERT_BIN_ARRAYS_EQUALS("fedcba9876543210", 16, buffer.buffer, buffer.len);
    aws_bigint_clean_up(&test);

    aws_byte_buf_clean_up(&buffer);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_from_uint64, s_test_bigint_from_uint64)
