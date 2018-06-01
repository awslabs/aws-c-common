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

static const uint8_t test_vector[] = {
    0xaa, 0xbb, 0xaa,
    0xbb, 0xcc, 0xbb,
    0x42,
    0x12, 0x34,
    0x45, 0x67, 0x89, 0xab,
    0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88
};

AWS_TEST_CASE(byte_cursor_write_tests, byte_cursor_write_tests_fn);
static int byte_cursor_write_tests_fn(struct aws_allocator *alloc, void *ctx) {
    uint8_t buf[sizeof(test_vector) + 1];
    memset(buf, 0, sizeof(buf));
    buf[sizeof(buf) - 1] = 0x99;

    struct aws_byte_cursor cur = aws_byte_cursor_from_array(buf, sizeof(buf) - 1);

    uint8_t aba[] = { 0xaa, 0xbb, 0xaa };
    uint8_t bcb[] = { 0xbb, 0xcc, 0xbb };

    ASSERT_TRUE(aws_byte_cursor_write(&cur, aba, sizeof(aba)));
    struct aws_byte_buf bcb_buf = aws_byte_buf_from_array(bcb, sizeof(bcb));
    ASSERT_TRUE(aws_byte_cursor_write_from_whole_buffer(&cur, &bcb_buf));
    ASSERT_TRUE(aws_byte_cursor_write_u8(&cur, 0x42));
    ASSERT_TRUE(aws_byte_cursor_write_be16(&cur, 0x1234));
    ASSERT_TRUE(aws_byte_cursor_write_be32(&cur, 0x456789ab));
    ASSERT_TRUE(aws_byte_cursor_write_be64(&cur, (uint64_t)0x1122334455667788ULL));

    ASSERT_FALSE(aws_byte_cursor_write_u8(&cur, 0xFF));
    ASSERT_UINT_EQUALS(0x99, buf[sizeof(buf) - 1]);

    ASSERT_BIN_ARRAYS_EQUALS(test_vector, sizeof(test_vector), buf, sizeof(test_vector));

    return 0;
}

AWS_TEST_CASE(byte_cursor_read_tests, byte_cursor_read_tests_fn);
static int byte_cursor_read_tests_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_byte_cursor cur = aws_byte_cursor_from_array(test_vector, sizeof(test_vector));

    uint8_t aba[3], bcb[3];
    ASSERT_TRUE(aws_byte_cursor_read(&cur, aba, sizeof(aba)));
    struct aws_byte_buf buf = aws_byte_buf_from_array(bcb, sizeof(bcb));
    ASSERT_TRUE(aws_byte_cursor_read_and_fill_buffer(&cur, &buf));
    uint8_t aba_expect[] = { 0xaa, 0xbb, 0xaa }, bcb_expect[] = { 0xbb, 0xcc, 0xbb };
    ASSERT_BIN_ARRAYS_EQUALS(aba_expect, 3, aba, 3);
    ASSERT_BIN_ARRAYS_EQUALS(bcb_expect, 3, bcb, 3);

    uint8_t u8; ASSERT_TRUE(aws_byte_cursor_read_u8(&cur, &u8)); ASSERT_UINT_EQUALS(u8, 0x42);
    uint16_t u16; ASSERT_TRUE(aws_byte_cursor_read_be16(&cur, &u16)); ASSERT_UINT_EQUALS(u16, 0x1234);
    uint32_t u32; ASSERT_TRUE(aws_byte_cursor_read_be32(&cur, &u32)); ASSERT_UINT_EQUALS(u32, 0x456789ab);
    uint64_t u64; ASSERT_TRUE(aws_byte_cursor_read_be64(&cur, &u64)); ASSERT_UINT_EQUALS(u64, (uint64_t)0x1122334455667788ULL);

    ASSERT_FALSE(aws_byte_cursor_read_u8(&cur, &u8));
    ASSERT_UINT_EQUALS(u8, 0x42);

    return 0;
}

AWS_TEST_CASE(byte_cursor_limit_tests, byte_cursor_limit_tests_fn);
static int byte_cursor_limit_tests_fn(struct aws_allocator *alloc, void *ctx) {
    uint8_t buf[] = { 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08 };
    uint8_t starting_buf[sizeof(buf)];
    memcpy(starting_buf, buf, sizeof(buf));

    struct aws_byte_cursor cur = aws_byte_cursor_from_array(buf, sizeof(buf));

    uint64_t u64 = 0;
    uint32_t u32 = 0;
    uint16_t u16 = 0;
    uint8_t u8 = 0;
    uint8_t arr[2] = {0};
    struct aws_byte_buf arrbuf = aws_byte_buf_from_array(arr, sizeof(arr));

    cur.len = 7;
    ASSERT_FALSE(aws_byte_cursor_read_be64(&cur, &u64)); ASSERT_UINT_EQUALS(0, u64);
    ASSERT_FALSE(aws_byte_cursor_write_be64(&cur, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    cur.len = 3;
    ASSERT_FALSE(aws_byte_cursor_read_be32(&cur, &u32)); ASSERT_UINT_EQUALS(0, u32);
    ASSERT_FALSE(aws_byte_cursor_write_be32(&cur, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    cur.len = 1;
    ASSERT_FALSE(aws_byte_cursor_read_be16(&cur, &u16)); ASSERT_UINT_EQUALS(0, u16);
    ASSERT_FALSE(aws_byte_cursor_write_be16(&cur, 0));
    ASSERT_FALSE(aws_byte_cursor_read(&cur, arr, sizeof(arr)));
    ASSERT_FALSE(aws_byte_cursor_write_from_whole_buffer(&cur, &arrbuf));
    ASSERT_FALSE(aws_byte_cursor_read_and_fill_buffer(&cur, &arrbuf));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));
    ASSERT_UINT_EQUALS(0, arr[0]); ASSERT_UINT_EQUALS(0, arr[1]);

    cur.len = 0;
    ASSERT_FALSE(aws_byte_cursor_read_u8(&cur, &u8)); ASSERT_UINT_EQUALS(0, u8);
    ASSERT_FALSE(aws_byte_cursor_write_u8(&cur, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    ASSERT_TRUE(aws_byte_cursor_read(&cur, arr, 0));
    ASSERT_TRUE(aws_byte_cursor_write(&cur, arr, 0));
    arrbuf.len = 0;
    ASSERT_TRUE(aws_byte_cursor_read_and_fill_buffer(&cur, &arrbuf));
    ASSERT_TRUE(aws_byte_cursor_write_from_whole_buffer(&cur, &arrbuf));
    ASSERT_UINT_EQUALS(0, arr[0]); ASSERT_UINT_EQUALS(0, arr[1]);

    return 0;
}
