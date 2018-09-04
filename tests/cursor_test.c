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

#ifndef SSIZE_MAX
#    define SSIZE_MAX (SIZE_MAX >> 1)
#endif

AWS_TEST_CASE(nospec_index_test, s_nospec_index_test_fn)
static int s_nospec_index_test_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(0, 1));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(0, 0));
    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(0, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(0, SIZE_MAX));

    ASSERT_UINT_EQUALS(0, aws_nospec_mask(1, 1));
    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(1, 2));
    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(1, 4));
    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(1, SIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(1, 0));

    ASSERT_UINT_EQUALS(0, aws_nospec_mask(4, 3));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(4, 4));
    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(4, 5));

    ASSERT_UINT_EQUALS(UINTPTR_MAX, aws_nospec_mask(SSIZE_MAX - 1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(SSIZE_MAX + 1, SSIZE_MAX));
    ASSERT_UINT_EQUALS(0, aws_nospec_mask(SSIZE_MAX, SSIZE_MAX + 1));

    return 0;
}

#define ASSERT_NOADVANCE(advlen, cursorlen)                                                                            \
    do {                                                                                                               \
        struct aws_byte_cursor cursor;                                                                                 \
        cursor.ptr = (uint8_t *)&cursor;                                                                               \
        cursor.len = (cursorlen);                                                                                      \
        struct aws_byte_cursor rv = advance(&cursor, (advlen));                                                        \
        ASSERT_NULL(rv.ptr, "advance(cursorlen=%s, advlen=%s) should fail", #cursorlen, #advlen);                      \
        ASSERT_UINT_EQUALS(0, rv.len, "advance(cursorlen=%s, advlen=%s) should fail", #cursorlen, #advlen);            \
    } while (0)

#define ASSERT_ADVANCE(advlen, cursorlen)                                                                              \
    do {                                                                                                               \
        uint8_t *orig_cursor;                                                                                          \
        struct aws_byte_cursor cursor;                                                                                 \
        cursor.len = (cursorlen);                                                                                      \
        cursor.ptr = orig_cursor = malloc(cursor.len);                                                                 \
        if (!cursor.ptr) {                                                                                             \
            abort();                                                                                                   \
        }                                                                                                              \
        struct aws_byte_cursor rv = advance(&cursor, (advlen));                                                        \
        ASSERT_PTR_EQUALS(orig_cursor, rv.ptr, "Wrong ptr in advance(cursorlen=%s, advlen=%s)", #cursorlen, #advlen);  \
        ASSERT_PTR_EQUALS(orig_cursor + (advlen), cursor.ptr, "Wrong new cursorptr in advance");                       \
        ASSERT_UINT_EQUALS((advlen), rv.len, "Wrong returned length");                                                 \
        ASSERT_UINT_EQUALS((cursorlen) - (advlen), cursor.len, "Wrong residual length");                               \
        free(orig_cursor);                                                                                             \
    } while (0)

static int s_test_byte_cursor_advance_internal(
    struct aws_byte_cursor (*advance)(struct aws_byte_cursor *cursor, size_t len)) {
    ASSERT_ADVANCE(0, 1);
    ASSERT_ADVANCE(1, 1);
    ASSERT_NOADVANCE(2, 1);

    ASSERT_ADVANCE(4, 5);
    ASSERT_ADVANCE(5, 5);
    ASSERT_NOADVANCE(6, 5);

    ASSERT_NOADVANCE(SSIZE_MAX + 1, SSIZE_MAX);
    ASSERT_NOADVANCE(SSIZE_MAX, (size_t)SSIZE_MAX + 1);

    return 0;
}

AWS_TEST_CASE(test_byte_cursor_advance, s_test_byte_cursor_advance_fn)
static int s_test_byte_cursor_advance_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    return s_test_byte_cursor_advance_internal(aws_byte_cursor_advance);
}

AWS_TEST_CASE(test_byte_cursor_advance_nospec, s_test_byte_cursor_advance_nospec_fn)
static int s_test_byte_cursor_advance_nospec_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    return s_test_byte_cursor_advance_internal(aws_byte_cursor_advance_nospec);
}

static const uint8_t TEST_VECTOR[] = {0xaa, 0xbb, 0xaa, 0xbb, 0xcc, 0xbb, 0x42, 0x12, 0x34, 0x45, 0x67,
                                      0x89, 0xab, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88};

AWS_TEST_CASE(byte_cursor_write_tests, s_byte_cursor_write_tests_fn);
static int s_byte_cursor_write_tests_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint8_t buf[sizeof(TEST_VECTOR) + 1];
    memset(buf, 0, sizeof(buf));
    buf[sizeof(buf) - 1] = 0x99;

    struct aws_byte_buf cur = aws_byte_buf_from_empty_array(buf, sizeof(buf) - 1);

    uint8_t aba[] = {0xaa, 0xbb, 0xaa};
    uint8_t bcb[] = {0xbb, 0xcc, 0xbb};

    ASSERT_TRUE(aws_byte_buf_write(&cur, aba, sizeof(aba)));
    struct aws_byte_buf bcb_buf = aws_byte_buf_from_array(bcb, sizeof(bcb));
    ASSERT_TRUE(aws_byte_buf_write_from_whole_buffer(&cur, bcb_buf));
    ASSERT_TRUE(aws_byte_buf_write_u8(&cur, 0x42));
    ASSERT_TRUE(aws_byte_buf_write_be16(&cur, 0x1234));
    ASSERT_TRUE(aws_byte_buf_write_be32(&cur, 0x456789ab));
    ASSERT_TRUE(aws_byte_buf_write_be64(&cur, (uint64_t)0x1122334455667788ULL));

    ASSERT_FALSE(aws_byte_buf_write_u8(&cur, 0xFF));
    ASSERT_UINT_EQUALS(0x99, buf[sizeof(buf) - 1]);

    ASSERT_BIN_ARRAYS_EQUALS(TEST_VECTOR, sizeof(TEST_VECTOR), buf, sizeof(TEST_VECTOR));

    return 0;
}

AWS_TEST_CASE(byte_cursor_read_tests, s_byte_cursor_read_tests_fn);
static int s_byte_cursor_read_tests_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_byte_cursor cur = aws_byte_cursor_from_array(TEST_VECTOR, sizeof(TEST_VECTOR));

    uint8_t aba[3], bcb[3];
    ASSERT_TRUE(aws_byte_cursor_read(&cur, aba, sizeof(aba)));
    struct aws_byte_buf buf = aws_byte_buf_from_empty_array(bcb, sizeof(bcb));
    ASSERT_TRUE(aws_byte_cursor_read_and_fill_buffer(&cur, &buf));
    uint8_t aba_expect[] = {0xaa, 0xbb, 0xaa}, bcb_expect[] = {0xbb, 0xcc, 0xbb};
    ASSERT_BIN_ARRAYS_EQUALS(aba_expect, 3, aba, 3);
    ASSERT_BIN_ARRAYS_EQUALS(bcb_expect, 3, bcb, 3);

    uint8_t u8;
    ASSERT_TRUE(aws_byte_cursor_read_u8(&cur, &u8));
    ASSERT_UINT_EQUALS(u8, 0x42);
    uint16_t u16;
    ASSERT_TRUE(aws_byte_cursor_read_be16(&cur, &u16));
    ASSERT_UINT_EQUALS(u16, 0x1234);
    uint32_t u32;
    ASSERT_TRUE(aws_byte_cursor_read_be32(&cur, &u32));
    ASSERT_UINT_EQUALS(u32, 0x456789ab);
    uint64_t u64;
    ASSERT_TRUE(aws_byte_cursor_read_be64(&cur, &u64));
    ASSERT_UINT_EQUALS(u64, (uint64_t)0x1122334455667788ULL);

    ASSERT_FALSE(aws_byte_cursor_read_u8(&cur, &u8));
    ASSERT_UINT_EQUALS(u8, 0x42);

    return 0;
}

AWS_TEST_CASE(byte_cursor_limit_tests, s_byte_cursor_limit_tests_fn);
static int s_byte_cursor_limit_tests_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint8_t buf[] = {0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08};
    uint8_t starting_buf[sizeof(buf)];
    memcpy(starting_buf, buf, sizeof(buf));

    struct aws_byte_cursor cur = aws_byte_cursor_from_array(buf, sizeof(buf));
    struct aws_byte_buf buffer = aws_byte_buf_from_empty_array(buf, sizeof(buf));

    uint64_t u64 = 0;
    uint32_t u32 = 0;
    uint16_t u16 = 0;
    uint8_t u8 = 0;
    uint8_t arr[2] = {0};
    struct aws_byte_buf arrbuf = aws_byte_buf_from_array(arr, sizeof(arr));

    cur.len = 7;
    buffer.capacity = 7;
    ASSERT_FALSE(aws_byte_cursor_read_be64(&cur, &u64));
    ASSERT_UINT_EQUALS(0, u64);
    ASSERT_FALSE(aws_byte_buf_write_be64(&buffer, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    cur.len = 3;
    buffer.capacity = 3;
    ASSERT_FALSE(aws_byte_cursor_read_be32(&cur, &u32));
    ASSERT_UINT_EQUALS(0, u32);
    ASSERT_FALSE(aws_byte_buf_write_be32(&buffer, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    cur.len = 1;
    buffer.capacity = 1;
    ASSERT_FALSE(aws_byte_cursor_read_be16(&cur, &u16));
    ASSERT_UINT_EQUALS(0, u16);
    ASSERT_FALSE(aws_byte_buf_write_be16(&buffer, 0));
    ASSERT_FALSE(aws_byte_cursor_read(&cur, arr, sizeof(arr)));
    ASSERT_FALSE(aws_byte_buf_write_from_whole_buffer(&buffer, arrbuf));
    ASSERT_FALSE(aws_byte_cursor_read_and_fill_buffer(&cur, &arrbuf));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));
    ASSERT_UINT_EQUALS(0, arr[0]);
    ASSERT_UINT_EQUALS(0, arr[1]);

    cur.len = 0;
    buffer.capacity = 0;
    ASSERT_FALSE(aws_byte_cursor_read_u8(&cur, &u8));
    ASSERT_UINT_EQUALS(0, u8);
    ASSERT_FALSE(aws_byte_buf_write_u8(&buffer, 0));
    ASSERT_BIN_ARRAYS_EQUALS(buf, sizeof(buf), starting_buf, sizeof(starting_buf));

    ASSERT_TRUE(aws_byte_cursor_read(&cur, arr, 0));
    ASSERT_TRUE(aws_byte_buf_write(&buffer, arr, 0));
    arrbuf.capacity = 0;
    ASSERT_TRUE(aws_byte_cursor_read_and_fill_buffer(&cur, &arrbuf));
    ASSERT_TRUE(aws_byte_buf_write_from_whole_buffer(&buffer, arrbuf));
    ASSERT_UINT_EQUALS(0, arr[0]);
    ASSERT_UINT_EQUALS(0, arr[1]);

    return 0;
}
