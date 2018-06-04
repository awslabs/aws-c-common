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


#include <aws/common/encoding.h>
#include <aws/testing/aws_test_harness.h>

/* Test cases from rfc4648 for Base 16 Encoding */

static int run_hex_encoding_test_case(struct aws_allocator *alloc, const char *test_str, size_t test_str_size,
                                      const char *expected, size_t expected_size) {
    size_t output_size = 0;

    ASSERT_SUCCESS(aws_hex_compute_encoded_len(test_str_size - 1, &output_size),
                   "compute hex encoded len failed with error %d", aws_last_error());
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on string should be %d", expected_size);

    char *allocation = (char *)aws_mem_acquire(alloc, output_size + 2);
    char *output_str = allocation + 1;
    memset(allocation, 0xdd, output_size + 2);

    struct aws_byte_buf to_encode = aws_byte_buf_from_c_str(test_str, test_str_size - 1);
    struct aws_byte_buf output = aws_byte_buf_from_c_str(output_str, output_size);
    ASSERT_SUCCESS(aws_hex_encode(&to_encode, &output), "encode call should have succeeded");

    ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, output_str, output_size, "Encode output should have been %s.", expected);
    ASSERT_INT_EQUALS((unsigned char)*allocation, (unsigned char)0xdd, "Write should not have occurred before the start of the buffer.");
    ASSERT_INT_EQUALS((unsigned char)*(allocation + output_size + 1), (unsigned char)0xdd, "Write should not have occurred after the start of the buffer.");

    ASSERT_SUCCESS(aws_hex_compute_decoded_len(expected_size - 1, &output_size),
                   "compute hex decoded len failed with error %d", aws_last_error());
    memset(allocation, 0xdd, output_size + 2);

    ASSERT_INT_EQUALS(test_str_size - 1, output_size, "Output size on string should be %d", test_str_size - 1);

    struct aws_byte_buf expected_buf = aws_byte_buf_from_c_str(expected, expected_size - 1);
    output = aws_byte_buf_from_c_str(output_str, output_size);
    ASSERT_SUCCESS(aws_hex_decode(&expected_buf, &output), "decode call should have succeeded");

    ASSERT_BIN_ARRAYS_EQUALS(test_str, test_str_size - 1, output_str, output_size, "Decode output should have been %s.", test_str);
    ASSERT_INT_EQUALS((unsigned char)*allocation, (unsigned char)0xdd, "Write should not have occurred before the start of the buffer.");
    ASSERT_INT_EQUALS((unsigned char)*(allocation + output_size + 1), (unsigned char)0xdd, "Write should not have occurred after the start of the buffer.");

    aws_mem_release(alloc, (void *)allocation);
    return 0;
}

static int hex_encoding_test_case_empty(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "";
    char expected[] = "";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_empty_test, hex_encoding_test_case_empty)


static int hex_encoding_test_case_f(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "f";
    char expected[] = "66";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_f_test, hex_encoding_test_case_f)

static int hex_encoding_test_case_fo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "fo";
    char expected[] = "666f";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_fo_test, hex_encoding_test_case_fo)


static int hex_encoding_test_case_foo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "foo";
    char expected[] = "666f6f";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_foo_test, hex_encoding_test_case_foo)


static int hex_encoding_test_case_foob(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foob";
    char expected[] = "666f6f62";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_foob_test, hex_encoding_test_case_foob)


static int hex_encoding_test_case_fooba(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "fooba";
    char expected[] = "666f6f6261";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_fooba_test, hex_encoding_test_case_fooba)

static int hex_encoding_test_case_foobar(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    char expected[] = "666f6f626172";

    return run_hex_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(hex_encoding_test_case_foobar_test, hex_encoding_test_case_foobar)


static int hex_encoding_test_case_missing_leading_zero_fn(struct aws_allocator *alloc, void *ctx) {

    uint8_t expected[] = { 0x01, 0x02, 0x03, 0x04 };
    char test_data[] = "1020304";

    uint8_t output[sizeof(expected)] = { 0 };

    struct aws_byte_buf test_buf = aws_byte_buf_from_c_str(test_data, sizeof(test_data) - 1);
    struct aws_byte_buf output_buf = aws_byte_buf_from_array(output, sizeof(expected));

    ASSERT_SUCCESS(aws_hex_decode(&test_buf, &output_buf), "Hex decoding failed with "
        "error code %d", aws_last_error());

    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), output, sizeof(output), "Hex decode expected output did not match actual output");

    return 0;
}

AWS_TEST_CASE(hex_encoding_test_case_missing_leading_zero, hex_encoding_test_case_missing_leading_zero_fn)

static int hex_encoding_invalid_buffer_size_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    size_t size_too_small = 2;
    char  output[] = {0, 0};

    struct aws_byte_buf test_buf = aws_byte_buf_from_c_str(test_data, sizeof(test_data));
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, size_too_small);

    ASSERT_ERROR(AWS_ERROR_SHORT_BUFFER, aws_hex_encode(&test_buf,
                                                               &output_buf),
        "Invalid buffer size should have failed with AWS_ERROR_SHORT_BUFFER");

    ASSERT_ERROR(AWS_ERROR_SHORT_BUFFER, aws_hex_decode(&test_buf,
                                                               &output_buf),
                 "Invalid buffer size should have failed with AWS_ERROR_SHORT_BUFFER");
    return 0;
}

AWS_TEST_CASE(hex_encoding_invalid_buffer_size_test, hex_encoding_invalid_buffer_size_test_fn)

static int hex_encoding_overflow_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    /* kill off the last two bits, so the not a multiple of 4 check doesn't trigger first */
    size_t overflow = (SIZE_MAX - 1);
    char  output[] = {0, 0};

    struct aws_byte_buf test_buf = aws_byte_buf_from_c_str(test_data, overflow);
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_OVERFLOW_DETECTED, aws_hex_encode(&test_buf,
                                                                &output_buf),
                 "overflow buffer size should have failed with AWS_ERROR_OVERFLOW_DETECTED");

    return 0;
}

AWS_TEST_CASE(hex_encoding_overflow_test, hex_encoding_overflow_test_fn)

static int hex_encoding_invalid_string_test_fn(struct aws_allocator *alloc, void *ctx) {

    char bad_input[] = "666f6f6x6172";
    uint8_t output[sizeof(bad_input)] = { 0 };

    struct aws_byte_buf bad_buf = aws_byte_buf_from_c_str(bad_input, sizeof(bad_input) - 1);
    struct aws_byte_buf output_buf = aws_byte_buf_from_array(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_INVALID_HEX_STR, aws_hex_decode(&bad_buf ,
                                                           &output_buf),
                 "An invalid string should have failed with AWS_ERROR_INVALID_HEX_STR");

    return 0;
}

AWS_TEST_CASE(hex_encoding_invalid_string_test, hex_encoding_invalid_string_test_fn)

/*base64 encoding test cases */
static int run_base64_encoding_test_case(struct aws_allocator *alloc, const char *test_str, size_t test_str_size,
                                      const char *expected, size_t expected_size) {
    size_t output_size = 0;

    /* Part 1: encoding */
    ASSERT_SUCCESS(aws_base64_compute_encoded_len(test_str_size, &output_size),
                   "Compute base64 encoded length failed with %d", aws_last_error());
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on string should be %d", expected_size);

    struct aws_byte_buf to_encode = aws_byte_buf_from_c_str(test_str, test_str_size);
    struct aws_byte_buf output;
    ASSERT_SUCCESS(aws_byte_buf_init(aws_default_allocator(), &output, output_size), "Memory allocation of output should have succeeded");

    ASSERT_SUCCESS(aws_base64_encode(&to_encode, &output), "encode call should have succeeded");

    ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, output.buffer, output_size, "Encode output should have been %s.", expected);

    aws_byte_buf_clean_up(&output);

    /* Part 2: decoding */

    ASSERT_SUCCESS(aws_base64_compute_decoded_len(expected, expected_size - 1, &output_size),
                  "Compute base64 decoded length failed with %d", aws_last_error());
    ASSERT_INT_EQUALS(test_str_size, output_size, "Output size on string should be %d", test_str_size);

    ASSERT_SUCCESS(aws_byte_buf_init(aws_default_allocator(), &output, output_size), "Memory allocation of output should have succeeded");

    struct aws_byte_buf expected_buf = aws_byte_buf_from_c_str(expected, expected_size - 1);
    ASSERT_SUCCESS(aws_base64_decode(&expected_buf, &output), "decode call should have succeeded");

    ASSERT_BIN_ARRAYS_EQUALS(test_str, test_str_size, output.buffer, output_size, "Decode output should have been %s.", test_str);

    aws_byte_buf_clean_up(&output);

    return 0;
}

static int base64_encoding_test_case_empty(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "";
    char expected[] = "";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_empty_test, base64_encoding_test_case_empty)


static int base64_encoding_test_case_f(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "f";
    char expected[] = "Zg==";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_f_test, base64_encoding_test_case_f)

static int base64_encoding_test_case_fo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "fo";
    char expected[] = "Zm8=";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_fo_test, base64_encoding_test_case_fo)


static int base64_encoding_test_case_foo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "foo";
    char expected[] = "Zm9v";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foo_test, base64_encoding_test_case_foo)


static int base64_encoding_test_case_foob(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foob";
    char expected[] = "Zm9vYg==";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foob_test, base64_encoding_test_case_foob)


static int base64_encoding_test_case_fooba(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "fooba";
    char expected[] = "Zm9vYmE=";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_fooba_test, base64_encoding_test_case_fooba)

static int base64_encoding_test_case_foobar(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    char expected[] = "Zm9vYmFy";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data) - 1, expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foobar_test, base64_encoding_test_case_foobar)

static int base64_encoding_test_zeros_fn(struct aws_allocator *alloc, void *ctx) {

    uint8_t test_data[6] = {0};
    char expected[] = "AAAAAAAA";

    return run_base64_encoding_test_case(alloc, (char *)test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_zeros, base64_encoding_test_zeros_fn)

/* this test is here because I manually touched the decoding table with sentinal values for efficiency reasons
 * and I want to make sure it matches the encoded string. This checks that none of those values that were previously 0 which
 * I moved to a sentinal value of 0xDD, were actually supposed to be a 0 other than character value of 65 -> "A" -> 0.
 */
static int base64_encoding_test_all_values_fn(struct aws_allocator *alloc, void *ctx) {

    uint8_t test_data[255] = {0};

    for(uint8_t i = 0; i < sizeof(test_data); ++i) {
        test_data[i] = i;
    }

    char expected[] =    "AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+P0BBQkNERU"
                         "ZHSElKS0xNTk9QUVJTVFVWV1hZWltcXV5fYGFiY2RlZmdoaWprbG1ub3BxcnN0dXZ3eHl6e3x9fn+AgYKDhIWGh4iJiouM"
                         "jY6PkJGSk5SVlpeYmZqbnJ2en6ChoqOkpaanqKmqq6ytrq+wsbKztLW2t7i5uru8vb6/wMHCw8TFxsfIycrLzM3Oz9DR0t"
                         "PU1dbX2Nna29zd3t/g4eLj5OXm5+jp6uvs7e7v8PHy8/T19vf4+fr7/P3+";

    return run_base64_encoding_test_case(alloc, (char *)test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_all_values, base64_encoding_test_all_values_fn)

static int base64_encoding_buffer_size_too_small_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    char encoded_data[] = "Zm9vYmFy";
    size_t size_too_small = 4;
    char  output[] = {0, 0};

    struct aws_byte_buf test_buf = aws_byte_buf_from_c_str(test_data, sizeof(test_data) - 1);
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, size_too_small);

    ASSERT_ERROR(AWS_ERROR_SHORT_BUFFER, aws_base64_encode(&test_buf,
                                                                  &output_buf),
                 "Invalid buffer size should have failed with AWS_ERROR_SHORT_BUFFER");

    struct aws_byte_buf encoded_buf = aws_byte_buf_from_c_str(encoded_data, sizeof(encoded_data) - 1);

    ASSERT_ERROR(AWS_ERROR_SHORT_BUFFER, aws_base64_decode(&encoded_buf,
                                                                   &output_buf),
                 "Invalid buffer size should have failed with AWS_ERROR_SHORT_BUFFER");
    return 0;
}

AWS_TEST_CASE(base64_encoding_buffer_size_too_small_test, base64_encoding_buffer_size_too_small_test_fn)


static int base64_encoding_buffer_size_overflow_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    char encoded_data[] = "Zm9vYmFy";
    /* kill off the last two bits, so the not a multiple of 4 check doesn't trigger first */
    size_t overflow = (SIZE_MAX - 1) & ~0x03;
    char  output[] = {0, 0};

    struct aws_byte_buf test_buf = aws_byte_buf_from_c_str(test_data, overflow + 2);
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_OVERFLOW_DETECTED, aws_base64_encode(&test_buf,
                                                                  &output_buf),
                 "overflow buffer size should have failed with AWS_ERROR_OVERFLOW_DETECTED");

    struct aws_byte_buf encoded_buf = aws_byte_buf_from_c_str(encoded_data, overflow);

    ASSERT_ERROR(AWS_ERROR_OVERFLOW_DETECTED, aws_base64_decode(&encoded_buf,
                                                                  &output_buf),
                 "overflow buffer size should have failed with AWS_ERROR_OVERFLOW_DETECTED");
    return 0;
}

AWS_TEST_CASE(base64_encoding_buffer_size_overflow_test, base64_encoding_buffer_size_overflow_test_fn)

static int base64_encoding_buffer_size_invalid_test_fn(struct aws_allocator *alloc, void *ctx) {

    char encoded_data[] = "Zm9vYmFy";
    /* kill off the last two bits, so the not a multiple of 4 check doesn't trigger first */
    char output[] = {0, 0};

    struct aws_byte_buf encoded_buf = aws_byte_buf_from_c_str(encoded_data, sizeof(encoded_data));
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_INVALID_BASE64_STR, aws_base64_decode(&encoded_buf, &output_buf),
                 "Non multiple of 4 buffer size should have failed with AWS_ERROR_INVALID_BASE64_STR");
    return 0;
}

AWS_TEST_CASE(base64_encoding_buffer_size_invalid_test, base64_encoding_buffer_size_invalid_test_fn)

static int base64_encoding_invalid_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    char encoded_data[] = "Z\n9vYmFy";
    char output[sizeof(encoded_data)] = {0};

    struct aws_byte_buf encoded_buf = aws_byte_buf_from_c_str(encoded_data, sizeof(encoded_data));
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_INVALID_BASE64_STR, aws_base64_decode(&encoded_buf,
                                                                 &output_buf),
                 "buffer with invalid character should have failed with AWS_ERROR_INVALID_BASE64_STR");
    return 0;
}

AWS_TEST_CASE(base64_encoding_invalid_buffer_test, base64_encoding_invalid_buffer_test_fn)

static int base64_encoding_invalid_padding_test_fn(struct aws_allocator *alloc, void *ctx) {

    char encoded_data[] = "Zm9vY===";
    char output[sizeof(encoded_data)] = {0};

    struct aws_byte_buf encoded_buf = aws_byte_buf_from_c_str(encoded_data, sizeof(encoded_data));
    struct aws_byte_buf output_buf = aws_byte_buf_from_c_str(output, sizeof(output));

    ASSERT_ERROR(AWS_ERROR_INVALID_BASE64_STR, aws_base64_decode(&encoded_buf,
                                                                 &output_buf),
                 "buffer with invalid padding should have failed with AWS_ERROR_INVALID_BASE64_STR");
    return 0;
}

AWS_TEST_CASE(base64_encoding_invalid_padding_test, base64_encoding_invalid_padding_test_fn)

/* network integer encoding tests */
static int uint64_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint64_t test_value = 0x1020304050607080;
    uint8_t buffer[8] = { 0 };
    aws_write_u64(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint64_t to buffer failed");

    uint64_t unmarshalled_value = aws_read_u64(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint64_buffer_test, uint64_buffer_test_fn)

static int uint64_buffer_non_aligned_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint64_t test_value = 0x1020304050607080;
    uint8_t *buffer = (uint8_t *)aws_mem_acquire(alloc, 9);

    ASSERT_FALSE((size_t)buffer & 0x07, "Heap allocated buffer should have been 8-byte aligned.");

    aws_write_u64(buffer + 1, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), (buffer + 1), sizeof(expected), "Uint64_t to buffer failed");

    uint64_t unmarshalled_value = aws_read_u64(buffer + 1);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    aws_mem_release(alloc, (void *)buffer);

    return 0;
}

AWS_TEST_CASE(uint64_buffer_non_aligned_test, uint64_buffer_non_aligned_test_fn)

static int uint32_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x10203040;
    uint8_t buffer[4] = { 0 };
    aws_write_u32(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint32_t to buffer failed");

    uint32_t unmarshalled_value = aws_read_u32(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint32_buffer_test, uint32_buffer_test_fn)

static int uint32_buffer_non_aligned_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x10203040;
    uint8_t *buffer = (uint8_t *)aws_mem_acquire(alloc, 9);

    ASSERT_FALSE((size_t)buffer & 0x07, "Heap allocated buffer should have been 8-byte aligned.");

    aws_write_u32(buffer + 5, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), (buffer + 5), sizeof(expected), "Uint32_t to buffer failed");

    uint64_t unmarshalled_value = aws_read_u32(buffer + 5);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    aws_mem_release(alloc, (void *)buffer);

    return 0;
}

AWS_TEST_CASE(uint32_buffer_non_aligned_test, uint32_buffer_non_aligned_test_fn)

static int uint24_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x102030;
    uint8_t buffer[3] = { 0 };
    aws_write_u24(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "24 bit int to buffer failed");

    uint32_t unmarshalled_value = aws_read_u24(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint24_buffer_test, uint24_buffer_test_fn)

static int uint24_buffer_non_aligned_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x102030;
    uint8_t *buffer = (uint8_t *)aws_mem_acquire(alloc, 9);

    ASSERT_FALSE((size_t)buffer & 0x07, "Heap allocated buffer should have been 8-byte aligned.");
    aws_write_u24(buffer + 6, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), (buffer + 6), sizeof(expected), "24 bit int to buffer failed");

    uint32_t unmarshalled_value = aws_read_u24(buffer + 6);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");
    aws_mem_release(alloc, (void *)buffer);

    return 0;
}

AWS_TEST_CASE(uint24_buffer_non_aligned_test, uint24_buffer_non_aligned_test_fn)

static int uint16_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint16_t test_value = 0x1020;
    uint8_t buffer[2] = { 0 };
    aws_write_u16(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");

    uint16_t unmarshalled_value = aws_read_u16(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_test, uint16_buffer_test_fn)

static int uint16_buffer_non_aligned_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint16_t test_value = 0x1020;
    uint8_t *buffer = (uint8_t *)aws_mem_acquire(alloc, 9);

    ASSERT_FALSE((size_t)buffer & 0x07, "Heap allocated buffer should have been 8-byte aligned.");
    aws_write_u16(buffer + 7, test_value);

    uint8_t expected[] = { 0x10, 0x20 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), (buffer + 7), sizeof(expected), "16 bit int to buffer failed");

    uint16_t unmarshalled_value = aws_read_u16(buffer + 7);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");
    aws_mem_release(alloc, (void *)buffer);

    return 0;
}

AWS_TEST_CASE(uint16_buffer_non_aligned_test, uint16_buffer_non_aligned_test_fn)


/* sanity check that signed/unsigned work the same */
static int uint16_buffer_signed_positive_test_fn(struct aws_allocator *alloc, void *ctx) {

    int16_t test_value = 0x4030;
    uint8_t buffer[2] = { 0 };
    aws_write_u16(buffer, (uint16_t)test_value);

    uint8_t expected[] = { 0x40, 0x30 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");

    int16_t unmarshalled_value = (int16_t)aws_read_u16(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_signed_positive_test, uint16_buffer_signed_positive_test_fn)

static int uint16_buffer_signed_negative_test_fn(struct aws_allocator *alloc, void *ctx) {

    int16_t test_value = -2;
    uint8_t buffer[2] = { 0 };
    aws_write_u16(buffer, (uint16_t)test_value);

    uint8_t expected[] = { 0xFF, 0xFE };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");

    int16_t unmarshalled_value = (int16_t)aws_read_u16(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_signed_negative_test, uint16_buffer_signed_negative_test_fn)
