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

struct bigint_uint64_init_test {
    uint64_t value;
    const char *expected_hex_serialization;
};

static struct bigint_uint64_init_test s_uint64_init_cases[] = {
    {
        .value = 0,
        .expected_hex_serialization = "0",
    },
    {
        .value = 1,
        .expected_hex_serialization = "1",
    },
    {
        .value = 128,
        .expected_hex_serialization = "80",
    },
    {
        .value = 255,
        .expected_hex_serialization = "ff",
    },
    {
        .value = UINT32_MAX,
        .expected_hex_serialization = "ffffffff",
    },
    {
        .value = (uint64_t)(UINT32_MAX) + 1,
        .expected_hex_serialization = "100000000",
    },
    {
        .value = UINT64_MAX,
        .expected_hex_serialization = "ffffffffffffffff",
    },
    {
        .value = 18364758544493064720ULL,
        .expected_hex_serialization = "fedcba9876543210",
    },
};

static int s_test_bigint_from_uint64(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_uint64_init_cases); ++i) {
        struct aws_byte_buf buffer;
        aws_byte_buf_init(&buffer, allocator, 1);

        struct aws_bigint test;

        struct bigint_uint64_init_test *testcase = &s_uint64_init_cases[i];

        size_t expected_length = strlen(testcase->expected_hex_serialization);

        aws_bigint_init_from_uint64(&test, allocator, testcase->value);
        ASSERT_TRUE(aws_bigint_is_positive(&test) == (testcase->value > 0));
        ASSERT_FALSE(aws_bigint_is_negative(&test));
        ASSERT_TRUE(aws_bigint_is_zero(&test) == (testcase->value == 0));
        ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
        ASSERT_TRUE(buffer.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(testcase->expected_hex_serialization, expected_length, buffer.buffer, buffer.len);

        aws_bigint_clean_up(&test);
        aws_byte_buf_clean_up(&buffer);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_from_uint64, s_test_bigint_from_uint64)

struct bigint_int64_init_test {
    int64_t value;
    const char *expected_hex_serialization;
};

static struct bigint_int64_init_test s_int64_init_cases[] = {
    {
        .value = 0,
        .expected_hex_serialization = "0",
    },
    {
        .value = 1,
        .expected_hex_serialization = "1",
    },
    {
        .value = -1,
        .expected_hex_serialization = "-1",
    },
    {
        .value = 128,
        .expected_hex_serialization = "80",
    },
    {
        .value = -128,
        .expected_hex_serialization = "-80",
    },
    {
        .value = 255,
        .expected_hex_serialization = "ff",
    },
    {
        .value = -255,
        .expected_hex_serialization = "-ff",
    },
    {
        .value = UINT32_MAX,
        .expected_hex_serialization = "ffffffff",
    },
    {
        .value = INT32_MAX,
        .expected_hex_serialization = "7fffffff",
    },
    {
        .value = INT32_MIN,
        .expected_hex_serialization = "-80000000",
    },
    {
        .value = (uint64_t)(UINT32_MAX) + 1,
        .expected_hex_serialization = "100000000",
    },
    {
        .value = INT64_MAX,
        .expected_hex_serialization = "7fffffffffffffff",
    },
    {
        .value = INT64_MIN,
        .expected_hex_serialization = "-8000000000000000",
    },
    {
        .value = 81985529216486895,
        .expected_hex_serialization = "123456789abcdef",
    },
};

static int s_test_bigint_from_int64(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_int64_init_cases); ++i) {
        struct aws_byte_buf buffer;
        aws_byte_buf_init(&buffer, allocator, 1);

        struct aws_bigint test;

        struct bigint_int64_init_test *testcase = &s_int64_init_cases[i];

        size_t expected_length = strlen(testcase->expected_hex_serialization);

        aws_bigint_init_from_int64(&test, allocator, testcase->value);
        ASSERT_TRUE(aws_bigint_is_positive(&test) == (testcase->value > 0));
        ASSERT_TRUE(aws_bigint_is_negative(&test) == (testcase->value < 0));
        ASSERT_TRUE(aws_bigint_is_zero(&test) == (testcase->value == 0));
        ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
        ASSERT_TRUE(buffer.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(testcase->expected_hex_serialization, expected_length, buffer.buffer, buffer.len);

        aws_bigint_clean_up(&test);
        aws_byte_buf_clean_up(&buffer);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_from_int64, s_test_bigint_from_int64)

struct bigint_string_init_success_test {
    const char *input_hex_value;
    const char *expected_hex_serialization;
    bool zero;
};

static struct bigint_string_init_success_test s_string_init_success_cases[] = {
    {
        .input_hex_value = "0",
        .expected_hex_serialization = "0",
        .zero = true,
    },
    {
        .input_hex_value = "0000000",
        .expected_hex_serialization = "0",
        .zero = true,
    },
    {
        .input_hex_value = "0x0000000",
        .expected_hex_serialization = "0",
        .zero = true,
    },
    {
        .input_hex_value = "0x00000001",
        .expected_hex_serialization = "1",
    },
    {
        .input_hex_value = "0x00000000000000000000000000000000000000000000000000000000000000001",
        .expected_hex_serialization = "1",
    },
    {
        .input_hex_value = "0x01000000000000000000000000000000000000000000000000000000000000001",
        .expected_hex_serialization = "1000000000000000000000000000000000000000000000000000000000000001",
    },
    {
        .input_hex_value = "0x07fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
        .expected_hex_serialization = "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe",
    },
    {
        .input_hex_value = "0x0abcdefABCDefabcdefabcdefabcdefabcdefabcdefabcdEFabcdefabcdefabcdefabcdEFAbcdef"
                           "abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdef",
        .expected_hex_serialization = "abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdef"
                                      "abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdef",
    },
    {
        .input_hex_value = "1234567890123456789012345678901234567890123456789012345678901234567890AbCFFDe",
        .expected_hex_serialization = "1234567890123456789012345678901234567890123456789012345678901234567890abcffde",
    },
};

static int s_test_bigint_from_hex_success(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_string_init_success_cases); ++i) {
        struct aws_byte_buf buffer;
        aws_byte_buf_init(&buffer, allocator, 1);

        struct aws_bigint test;

        struct bigint_string_init_success_test *testcase = &s_string_init_success_cases[i];

        size_t expected_length = strlen(testcase->expected_hex_serialization);

        ASSERT_SUCCESS(
            aws_bigint_init_from_hex(&test, allocator, aws_byte_cursor_from_c_str(testcase->input_hex_value)));
        ASSERT_TRUE(aws_bigint_is_positive(&test) == !testcase->zero);
        ASSERT_FALSE(aws_bigint_is_negative(&test));
        ASSERT_TRUE(aws_bigint_is_zero(&test) == testcase->zero);
        ASSERT_SUCCESS(aws_bigint_bytebuf_append_as_hex(&test, &buffer));
        ASSERT_TRUE(buffer.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(testcase->expected_hex_serialization, expected_length, buffer.buffer, buffer.len);

        aws_bigint_clean_up(&test);
        aws_byte_buf_clean_up(&buffer);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_from_hex_success, s_test_bigint_from_hex_success)

static const char *s_string_init_failure_cases[] = {
    "000000AFG",
    "xcde",
    "120xff",
    "#56",
    "-800", // debatable if we should allow negative prefix
    "0xx7f",
    "0000x00000",
};

static int s_test_bigint_from_hex_failure(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_string_init_failure_cases); ++i) {
        struct aws_byte_buf buffer;
        aws_byte_buf_init(&buffer, allocator, 1);

        struct aws_bigint test;

        const char *testcase = s_string_init_failure_cases[i];

        ASSERT_FAILS(aws_bigint_init_from_hex(&test, allocator, aws_byte_cursor_from_c_str(testcase)));

        aws_byte_buf_clean_up(&buffer);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_from_hex_failure, s_test_bigint_from_hex_failure)