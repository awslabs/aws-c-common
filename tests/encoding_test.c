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
