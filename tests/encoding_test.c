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
#include <aws_test_harness.h>

/* Test cases from rfc4648 for Base 16 Encoding */

static int run_hex_encoding_test_case(struct aws_allocator *alloc, const char *test_str, size_t test_str_size,
                                      const char *expected, size_t expected_size) {
    size_t output_size = 0;

    char *output_str = NULL;

    ASSERT_SUCCESS(aws_hex_encode((uint8_t *)test_str, test_str_size - 1, NULL, &output_size), "encode call should have succeeded");
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on string should be %d", expected_size);

    output_str = (char *)aws_mem_acquire(alloc, output_size);
    memset(output_str, 0, output_size);

    ASSERT_SUCCESS(aws_hex_encode((uint8_t *)test_str, test_str_size - 1, output_str, &output_size), "encode call should have succeeded");
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on an empty string should be %d", expected_size);

    ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, output_str, output_size, "Encode output should have been %s.", expected);

    ASSERT_SUCCESS(aws_hex_decode(expected, expected_size - 1, NULL, &output_size), "decode call should have succeeded");
    ASSERT_INT_EQUALS(test_str_size - 1, output_size, "Output size on string should be %d", test_str_size - 1);

    memset(output_str, 0, output_size);

    ASSERT_SUCCESS(aws_hex_decode(expected, expected_size - 1, (uint8_t *)output_str, &output_size), "decode call should have succeeded");
    ASSERT_INT_EQUALS(test_str_size - 1, output_size, "Output size of string should be %d", test_str_size - 1);

    ASSERT_BIN_ARRAYS_EQUALS(test_str, test_str_size - 1, output_str, output_size, "Decode output should have been %s.", test_str);

    aws_mem_release(alloc, (void *)output_str);
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

static int hex_encoding_invalid_buffer_size_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    size_t size_too_small = 2;
    char  output_buff[] = {0, 0};

    ASSERT_ERROR(AWS_ERROR_INVALID_BUFFER_SIZE, aws_hex_encode((const uint8_t *)test_data, sizeof(test_data),
                                                               output_buff, &size_too_small),
        "Invalid buffer size should have failed with AWS_ERROR_INVALID_BUFFER_SIZE");

    ASSERT_ERROR(AWS_ERROR_INVALID_BUFFER_SIZE, aws_hex_decode(test_data, sizeof(test_data),
                                                               test_data, &size_too_small),
                 "Invalid buffer size should have failed with AWS_ERROR_INVALID_BUFFER_SIZE");
    return 0;
}

AWS_TEST_CASE(hex_encoding_invalid_buffer_size_test, hex_encoding_invalid_buffer_size_test_fn)

/*base64 encoding test cases */
static int run_base64_encoding_test_case(struct aws_allocator *alloc, const char *test_str, size_t test_str_size,
                                      const char *expected, size_t expected_size) {
    size_t output_size = 0;

    char *output_str = NULL;

    ASSERT_SUCCESS(aws_base64_encode((uint8_t *)test_str, test_str_size - 1, NULL, &output_size), "encode call should have succeeded");
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on string should be %d", expected_size);

    output_str = (char *)aws_mem_acquire(alloc, output_size);
    memset(output_str, 0, output_size);

    ASSERT_SUCCESS(aws_base64_encode((uint8_t *)test_str, test_str_size - 1, output_str, &output_size), "encode call should have succeeded");
    ASSERT_INT_EQUALS(expected_size, output_size, "Output size on an empty string should be %d", expected_size);

    ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, output_str, output_size, "Encode output should have been %s.", expected);

    ASSERT_SUCCESS(aws_base64_decode(expected, expected_size - 1, NULL, &output_size), "decode call should have succeeded");
    ASSERT_INT_EQUALS(test_str_size - 1, output_size, "Output size on string should be %d", test_str_size - 1);

    memset(output_str, 0, output_size);

    ASSERT_SUCCESS(aws_base64_decode(expected, expected_size - 1, (uint8_t *)output_str, &output_size), "decode call should have succeeded");
    ASSERT_INT_EQUALS(test_str_size - 1, output_size, "Output size of string should be %d", test_str_size - 1);

    ASSERT_BIN_ARRAYS_EQUALS(test_str, test_str_size - 1, output_str, output_size, "Decode output should have been %s.", test_str);

    aws_mem_release(alloc, (void *)output_str);
    return 0;
}

static int base64_encoding_test_case_empty(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "";
    char expected[] = "";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_empty_test, base64_encoding_test_case_empty)


static int base64_encoding_test_case_f(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "f";
    char expected[] = "Zg==";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_f_test, base64_encoding_test_case_f)

static int base64_encoding_test_case_fo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "fo";
    char expected[] = "Zm8=";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_fo_test, base64_encoding_test_case_fo)


static int base64_encoding_test_case_foo(struct aws_allocator *alloc, void *ctx) {
    char test_data[] = "foo";
    char expected[] = "Zm9v";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foo_test, base64_encoding_test_case_foo)


static int base64_encoding_test_case_foob(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foob";
    char expected[] = "Zm9vYg==";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foob_test, base64_encoding_test_case_foob)


static int base64_encoding_test_case_fooba(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "fooba";
    char expected[] = "Zm9vYmE=";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_fooba_test, base64_encoding_test_case_fooba)

static int base64_encoding_test_case_foobar(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    char expected[] = "Zm9vYmFy";

    return run_base64_encoding_test_case(alloc, test_data, sizeof(test_data), expected, sizeof(expected));
}

AWS_TEST_CASE(base64_encoding_test_case_foobar_test, base64_encoding_test_case_foobar)

static int base64_encoding_invalid_buffer_size_test_fn(struct aws_allocator *alloc, void *ctx) {

    char test_data[] = "foobar";
    size_t size_too_small = 2;
    char  output_buff[] = {0, 0};

    ASSERT_ERROR(AWS_ERROR_INVALID_BUFFER_SIZE, aws_base64_encode((const uint8_t *)test_data, sizeof(test_data),
                                                                  output_buff, &size_too_small),
                 "Invalid buffer size should have failed with AWS_ERROR_INVALID_BUFFER_SIZE");

    ASSERT_ERROR(AWS_ERROR_INVALID_BUFFER_SIZE, aws_base64_decode(test_data, sizeof(test_data),
                                                                  test_data, &size_too_small),
                 "Invalid buffer size should have failed with AWS_ERROR_INVALID_BUFFER_SIZE");
    return 0;
}

AWS_TEST_CASE(base64_encoding_invalid_buffer_size_test, base64_encoding_invalid_buffer_size_test_fn)

static int uint64_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint64_t test_value = 0x1020304050607080;
    uint8_t buffer[8] = { 0 };
    uint8_t *new_ptr = aws_add_uint64_to_buffer(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint64_t to buffer failed");
    ASSERT_INT_EQUALS(buffer + sizeof(uint64_t), new_ptr, "Buffer offset was incorrect");

    uint64_t unmarshalled_value = aws_uint64_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint64_buffer_test, uint64_buffer_test_fn)

static int uint32_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x10203040;
    uint8_t buffer[4] = { 0 };
    uint8_t *new_ptr = aws_add_uint32_to_buffer(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30, 0x40 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint32_t to buffer failed");
    ASSERT_INT_EQUALS(buffer + sizeof(uint32_t), new_ptr, "Buffer offset was incorrect");

    uint32_t unmarshalled_value = aws_uint32_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint32_buffer_test, uint32_buffer_test_fn)

static int uint24_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint32_t test_value = 0x102030;
    uint8_t buffer[3] = { 0 };
    uint8_t *new_ptr = aws_add_uint24_to_buffer(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20, 0x30 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "24 bit int to buffer failed");
    ASSERT_INT_EQUALS(buffer + 3, new_ptr, "Buffer offset was incorrect");

    uint32_t unmarshalled_value = aws_uint24_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint24_buffer_test, uint24_buffer_test_fn)

static int uint16_buffer_test_fn(struct aws_allocator *alloc, void *ctx) {

    uint16_t test_value = 0x1020;
    uint8_t buffer[2] = { 0 };
    uint8_t *new_ptr = aws_add_uint16_to_buffer(buffer, test_value);

    uint8_t expected[] = { 0x10, 0x20 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");
    ASSERT_INT_EQUALS(buffer + sizeof(uint16_t), new_ptr, "Buffer offset was incorrect");

    uint16_t unmarshalled_value = aws_uint16_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_test, uint16_buffer_test_fn)

/* sanity check that signed/unsigned work the same */
static int uint16_buffer_signed_positive_test_fn(struct aws_allocator *alloc, void *ctx) {

    int16_t test_value = 0x4030;
    uint8_t buffer[2] = { 0 };
    uint8_t *new_ptr = aws_add_uint16_to_buffer(buffer, (uint16_t)test_value);

    uint8_t expected[] = { 0x40, 0x30 };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");
    ASSERT_INT_EQUALS(buffer + sizeof(uint16_t), new_ptr, "Buffer offset was incorrect");

    int16_t unmarshalled_value = (int16_t)aws_uint16_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_signed_positive_test, uint16_buffer_signed_positive_test_fn)

static int uint16_buffer_signed_negative_test_fn(struct aws_allocator *alloc, void *ctx) {

    int16_t test_value = -2;
    uint8_t buffer[2] = { 0 };
    uint8_t *new_ptr = aws_add_uint16_to_buffer(buffer, (uint16_t)test_value);

    uint8_t expected[] = { 0xFF, 0xFE };
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected), buffer, sizeof(buffer), "Uint16_t to buffer failed");
    ASSERT_INT_EQUALS(buffer + sizeof(uint16_t), new_ptr, "Buffer offset was incorrect");

    int16_t unmarshalled_value = (int16_t)aws_uint16_from_buffer(buffer);
    ASSERT_INT_EQUALS(test_value, unmarshalled_value, "After unmarshalling the encoded data, it didn't match");

    return 0;
}

AWS_TEST_CASE(uint16_buffer_signed_negative_test, uint16_buffer_signed_negative_test_fn)
