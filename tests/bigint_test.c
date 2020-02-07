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
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&test, &buffer));
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
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&test, &buffer));
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
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&test, &buffer));
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

struct bigint_comparison_test {
    const char *value1;
    const char *value2;
    bool is_negative1;
    bool is_negative2;
};

static struct bigint_comparison_test s_equality_cases[] = {
    {
        .value1 = "0",
        .value2 = "0x00000",
    },
    {
        .value1 = "0FF",
        .value2 = "0x00FF",
    },
    {
        .value1 = "A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "000000000000A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
    },
    {
        .value1 = "A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "000000000000A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .is_negative1 = true,
        .is_negative2 = true,
    },
};

static int s_test_bigint_equality(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_equality_cases); ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_comparison_test *testcase = &s_equality_cases[i];

        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        ASSERT_TRUE(aws_bigint_equals(&value1, &value2));
        ASSERT_TRUE(aws_bigint_equals(&value2, &value1));
        ASSERT_FALSE(aws_bigint_not_equals(&value1, &value2));
        ASSERT_FALSE(aws_bigint_not_equals(&value2, &value1));

        if (!aws_bigint_is_zero(&value1)) {
            aws_bigint_negate(&value1);

            ASSERT_FALSE(aws_bigint_equals(&value1, &value2));
            ASSERT_FALSE(aws_bigint_equals(&value2, &value1));

            aws_bigint_negate(&value2);

            ASSERT_TRUE(aws_bigint_equals(&value1, &value2));
            ASSERT_TRUE(aws_bigint_equals(&value2, &value1));
        }

        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_equality, s_test_bigint_equality)

static struct bigint_comparison_test s_inequality_cases[] = {
    {
        .value1 = "0",
        .value2 = "0x00001",
    },
    {
        .value1 = "1",
        .value2 = "0x00001",
        .is_negative2 = true,
    },
    {
        .value1 = "0FF",
        .value2 = "0x00FF",
        .is_negative1 = true,
    },
    {
        .value1 = "0xabcdef987654321",
        .value2 = "accdef987654321",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 = "B9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "000000000000A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
    },
    {
        .value1 = "FFFFFFFFFFFFFFFF",
        .value2 = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    },
};

static int s_test_bigint_inequality(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_inequality_cases); ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_comparison_test *testcase = &s_inequality_cases[i];

        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        ASSERT_FALSE(aws_bigint_equals(&value1, &value2));
        ASSERT_FALSE(aws_bigint_equals(&value2, &value1));
        ASSERT_TRUE(aws_bigint_not_equals(&value1, &value2));
        ASSERT_TRUE(aws_bigint_not_equals(&value2, &value1));

        aws_bigint_negate(&value1);
        aws_bigint_negate(&value2);

        ASSERT_FALSE(aws_bigint_equals(&value1, &value2));
        ASSERT_FALSE(aws_bigint_equals(&value2, &value1));
        ASSERT_TRUE(aws_bigint_not_equals(&value1, &value2));
        ASSERT_TRUE(aws_bigint_not_equals(&value2, &value1));

        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_inequality, s_test_bigint_inequality)

static struct bigint_comparison_test s_less_than_cases[] = {
    {
        .value1 = "0",
        .value2 = "0x00001",
    },
    {
        .value1 = "1",
        .value2 = "0x100000000000000000000000000000000001",
    },
    {
        .value1 = "0x00002",
        .value2 = "1",
        .is_negative1 = true,
    },
    {
        .value1 = "0FF",
        .value2 = "0x00FF",
        .is_negative1 = true,
    },
    {
        .value1 = "0FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        .value2 = "0x00FF",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 = "0xabcdef987654321",
        .value2 = "accdef987654321",
    },
    {
        .value1 = "000000000000A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "B9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
    },
    {
        .value1 = "000000000000B9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 = "FFFFFFFFFFFFFFFF",
        .value2 = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    },
    {
        .value1 = "00000001FFFFFFFF",
        .value2 = "FFFFFFFF00000001",
    },
};

static int s_test_bigint_less_than(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_less_than_cases); ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_comparison_test *testcase = &s_less_than_cases[i];

        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        /* a < b */
        ASSERT_TRUE(aws_bigint_less_than(&value1, &value2));
        ASSERT_FALSE(aws_bigint_greater_than_or_equals(&value1, &value2));

        aws_bigint_negate(&value1);
        aws_bigint_negate(&value2);

        /* !(-a < -b) */
        ASSERT_FALSE(aws_bigint_less_than(&value1, &value2));
        ASSERT_TRUE(aws_bigint_greater_than_or_equals(&value1, &value2));

        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_less_than, s_test_bigint_less_than)

static struct bigint_comparison_test s_greater_than_cases[] = {
    {
        .value1 = "0x56",
        .value2 = "0x00001",
    },
    {
        .value1 = "0x56",
        .value2 = "0x00001",
        .is_negative2 = true,
    },
    {
        .value1 = "0x100000000000000000000000000000000001",
        .value2 = "1",
    },
    {
        .value1 = "0FF",
        .value2 = "0x00FFFF",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 = "0FF",
        .value2 = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 = "accdef987654321",
        .value2 = "0xabcdef987654321",
    },
    {
        .value1 = "B9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "000000000000A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
    },
    {
        .value1 = "A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .value2 = "000000000000B9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4A9B8C7D6E5F4",
        .is_negative1 = true,
        .is_negative2 = true,

    },
    {
        .value1 = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        .value2 = "FFFFFFFFFFFFFFFF",
    },
    {
        .value1 = "ABCDEF9800000002",
        .value2 = "1000000212345678",
    },
};

static int s_test_bigint_greater_than(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    for (size_t i = 0; i < AWS_ARRAY_SIZE(s_greater_than_cases); ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_comparison_test *testcase = &s_greater_than_cases[i];

        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        /* a < b */
        ASSERT_TRUE(aws_bigint_greater_than(&value1, &value2));
        ASSERT_FALSE(aws_bigint_less_than_or_equals(&value1, &value2));

        aws_bigint_negate(&value1);
        aws_bigint_negate(&value2);

        /* !(-a < -b) */
        ASSERT_FALSE(aws_bigint_greater_than(&value1, &value2));
        ASSERT_TRUE(aws_bigint_less_than_or_equals(&value1, &value2));

        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_bigint_greater_than, s_test_bigint_greater_than)

struct bigint_arithmetic_test {
    const char *value1;
    const char *value2;
    const char *expected_result;
    bool is_negative1;
    bool is_negative2;
};

/*
 * Checks (val1 + val2), (val2 + val1) against expected result as a string
 * Checks (-val1 + -val2), (-val2 + -val1) against -(val1 + val2)
 */
static int s_do_addition_test(
    struct aws_allocator *allocator,
    struct bigint_arithmetic_test *test_cases,
    size_t test_case_count) {

    struct aws_byte_buf serialized_sum;
    aws_byte_buf_init(&serialized_sum, allocator, 0);

    for (size_t i = 0; i < test_case_count; ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_arithmetic_test *testcase = &test_cases[i];

        /* init operands */
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        /* add and test val1 + val2 */
        struct aws_bigint sum;
        aws_bigint_init_from_uint64(&sum, allocator, 0);

        aws_bigint_add(&sum, &value1, &value2);

        serialized_sum.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&sum, &serialized_sum));

        size_t expected_length = strlen(testcase->expected_result);
        ASSERT_TRUE(serialized_sum.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(testcase->expected_result, expected_length, serialized_sum.buffer, serialized_sum.len);

        aws_bigint_clean_up(&sum);

        /* add and test val2 + val1 */
        aws_bigint_init_from_uint64(&sum, allocator, 0);

        aws_bigint_add(&sum, &value2, &value1);

        serialized_sum.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&sum, &serialized_sum));

        ASSERT_TRUE(serialized_sum.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(testcase->expected_result, expected_length, serialized_sum.buffer, serialized_sum.len);

        /* aliasing tests*/

        /* test val1 += val2 */
        struct aws_bigint value1_copy;
        aws_bigint_init_from_copy(&value1_copy, &value1);

        aws_bigint_add(&value1_copy, &value1_copy, &value2);
        ASSERT_TRUE(aws_bigint_equals(&value1_copy, &sum));

        /* test val2 += val1 */
        struct aws_bigint value2_copy;
        aws_bigint_init_from_copy(&value2_copy, &value2);

        aws_bigint_add(&value2_copy, &value1, &value2_copy);
        ASSERT_TRUE(aws_bigint_equals(&value2_copy, &sum));

        /* negation tests */
        struct aws_bigint negated_sum;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&negated_sum, &sum));
        aws_bigint_negate(&negated_sum);

        aws_bigint_negate(&value1);
        aws_bigint_negate(&value2);

        /* add and test -val1 + -val2 */
        struct aws_bigint sum_of_negations;
        aws_bigint_init_from_uint64(&sum_of_negations, allocator, 0);

        aws_bigint_add(&sum_of_negations, &value1, &value2);
        ASSERT_TRUE(aws_bigint_equals(&sum_of_negations, &negated_sum));

        /* add and test -val2 + -val1 */
        aws_bigint_clean_up(&sum_of_negations);
        aws_bigint_init_from_uint64(&sum_of_negations, allocator, 0);

        aws_bigint_add(&sum_of_negations, &value2, &value1);
        ASSERT_TRUE(aws_bigint_equals(&sum_of_negations, &negated_sum));

        aws_bigint_clean_up(&value1_copy);
        aws_bigint_clean_up(&value2_copy);
        aws_bigint_clean_up(&sum_of_negations);
        aws_bigint_clean_up(&negated_sum);
        aws_bigint_clean_up(&sum);
        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    aws_byte_buf_clean_up(&serialized_sum);

    return AWS_OP_SUCCESS;
}

/* clang-format off */
static struct bigint_arithmetic_test s_add_zero_test_cases[] = {
    {
        .value1 =       "0x00",
        .value2 =          "0",
        .expected_result = "0",
    },
    {
        .value1 =         "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .value2 =                                                                      "0",
        .expected_result = "-ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .is_negative1 = true,
    },
    {
        .value1 =        "0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef012",
        .value2 =                                                                                                  "0",
        .expected_result = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef012",
    },
};
/* clang-format on */

static int s_test_bigint_add_zero(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_addition_test(allocator, s_add_zero_test_cases, AWS_ARRAY_SIZE(s_add_zero_test_cases));
}

AWS_TEST_CASE(test_bigint_add_zero, s_test_bigint_add_zero)

/* clang-format off */
static struct bigint_arithmetic_test s_add_positive_test_cases[] = {
    {
        .value1 =       "0x01",
        .value2 =          "1",
        .expected_result = "2",
    },
    {
        .value1 =        "0x76543210765432107654321076543210765432107654321076543210",
        .value2 =          "3557799b3557799b3557799b3557799b3557799b3557799b3557799b",
        .expected_result = "abababababababababababababababababababababababababababab",
    },
    {
        .value1 =         "0xffffffff",
        .value2 =                  "1",
        .expected_result = "100000000",
    },
    {
        .value1 =         "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .value2 =                                                                      "1",
        .expected_result = "1000000000000000000000000000000000000000000000000000000000000",
    },
    {
        .value1 =         "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .value2 =                                                              "1FFFFFFFF",
        .expected_result = "10000000000000000000000000000000000000000000000000001fffffffe",
    },
    {
        .value1 =         "0x8000000080000000800000008000000080000000",
        .value2 =         "0x8000000080000000800000008000000080000000",
        .expected_result = "10000000100000001000000010000000100000000",
    },
};
/* clang-format on */

static int s_test_bigint_add_positive(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;

    return s_do_addition_test(allocator, s_add_positive_test_cases, AWS_ARRAY_SIZE(s_add_positive_test_cases));
}

AWS_TEST_CASE(test_bigint_add_positive, s_test_bigint_add_positive)

/* clang-format off */
static struct bigint_arithmetic_test s_add_negative_test_cases[] = {
    {
        .value1 =        "0x01",
        .value2 =           "1",
        .expected_result = "-2",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 =          "0xfffffff0ffffffff",
        .value2 =                  "1100000001",
        .expected_result = "-10000000200000000",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 =         "0x11111111111111222222222222333333333344444444555555666677",
        .value2 =           "123456789abcde23456789abcd3456789abc456789ab56789a678978",
        .expected_result = "-23456789abcdef456789abcdef6789abcdef89abcdefabcdefcdefef",
        .is_negative1 = true,
        .is_negative2 = true,
    },
};
/* clang-format on */

static int s_test_bigint_add_negative(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_addition_test(allocator, s_add_negative_test_cases, AWS_ARRAY_SIZE(s_add_negative_test_cases));
}

AWS_TEST_CASE(test_bigint_add_negative, s_test_bigint_add_negative)

/* clang-format off */
static struct bigint_arithmetic_test s_add_mixed_test_cases[] = {
    {
        .value1 =       "0x01",
        .value2 =          "1",
        .expected_result = "0",
        .is_negative1 = true,
    },
    {
        .value1 = "0xabcdef0123456789abcdef0123456789abcdef0123456789",
        .value2 =   "abcdef0123456789abcdef0123456789abcdef0123456789",
        .expected_result =                                         "0",
        .is_negative2 = true,
    },
    {
        .value1 =          "1000000000000000000000000000000000000000000000000000000000000000000000000000",
        .value2 =           "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .expected_result =                                                                            "1",
        .is_negative2 = true,
    },
    {
        .value1 =          "1000000000000000000000000000000000000000000000000000000000000000000000000000",
        .value2 =                                                                                     "1",
        .expected_result =  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .is_negative2 = true,
    },
    {
        .value1 =          "100000000000000000000000000000000000000000000000000000000000000000000000",
        .value2 =                                                                                 "1",
        .expected_result =  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .is_negative2 = true,
    },
    {
        .value1 =          "9999999999999999999999999999999999999999999999999997",
        .value2 =          "9999999999999999999999999999999999999999999999999999",
        .expected_result =                                                    "2",
        .is_negative1 = true,
    },
    {
        .value1 =          "ddddddddddddddeeeeeeeeeeeeeeeffffffffffffffff",
        .value2 =          "0123456789abcd0123456789abcde0123456789abcdef",
        .expected_result = "dcba9876543210edcba9876543210fedcba9876543210",
        .is_negative2 = true,
    },
    {
        .value1 =          "10123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789a",
        .value2 =           "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        .expected_result =   "123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789b",
        .is_negative2 = true,
    },
    {
        .value1 =       "0x040",
        .value2 =          "42",
        .expected_result = "-2",
        .is_negative2 = true,
    },
};
/* clang-format on */

static int s_test_bigint_add_mixed_sign(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_addition_test(allocator, s_add_mixed_test_cases, AWS_ARRAY_SIZE(s_add_mixed_test_cases));
}

AWS_TEST_CASE(test_bigint_add_mixed_sign, s_test_bigint_add_mixed_sign)

/*
 * Checks (val1 - val2) against expected result as a string
 * Checks (val2 - val1), (-val1 - -val2), (-val2 - -val1) against +/-(val1 - val2)
 */
static int s_do_subtraction_test(
    struct aws_allocator *allocator,
    struct bigint_arithmetic_test *test_cases,
    size_t test_case_count) {

    struct aws_byte_buf serialized_diff;
    aws_byte_buf_init(&serialized_diff, allocator, 0);

    for (size_t i = 0; i < test_case_count; ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_arithmetic_test *testcase = &test_cases[i];

        /* init operands */
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        /* test val1 - val2 */
        struct aws_bigint diff;
        aws_bigint_init_from_uint64(&diff, allocator, 0);

        aws_bigint_subtract(&diff, &value1, &value2);

        serialized_diff.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&diff, &serialized_diff));

        size_t expected_length = strlen(testcase->expected_result);
        ASSERT_TRUE(serialized_diff.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(
            testcase->expected_result, expected_length, serialized_diff.buffer, serialized_diff.len);

        struct aws_bigint negated_diff;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&negated_diff, &diff));
        aws_bigint_negate(&negated_diff);

        /* test val2 - val1 */
        struct aws_bigint result;
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_subtract(&result, &value2, &value1);

        ASSERT_TRUE(aws_bigint_equals(&result, &negated_diff));

        /* aliasing tests*/

        /* test val1 -= val2 */
        struct aws_bigint value1_copy;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&value1_copy, &value1));

        ASSERT_SUCCESS(aws_bigint_subtract(&value1_copy, &value1_copy, &value2));
        ASSERT_TRUE(aws_bigint_equals(&value1_copy, &diff));

        /* test val2 = val1 - val2 */
        struct aws_bigint value2_copy;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&value2_copy, &value2));

        ASSERT_SUCCESS(aws_bigint_subtract(&value2_copy, &value1, &value2_copy));
        ASSERT_TRUE(aws_bigint_equals(&value2_copy, &diff));

        /* negation tests */
        aws_bigint_negate(&value1);
        aws_bigint_negate(&value2);

        /* test -val1 - -val2 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_subtract(&result, &value1, &value2);
        ASSERT_TRUE(aws_bigint_equals(&result, &negated_diff));

        /* test -val2 - -val1 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_subtract(&result, &value2, &value1);
        ASSERT_TRUE(aws_bigint_equals(&result, &diff));

        aws_bigint_clean_up(&value1_copy);
        aws_bigint_clean_up(&value2_copy);
        aws_bigint_clean_up(&result);
        aws_bigint_clean_up(&negated_diff);
        aws_bigint_clean_up(&diff);
        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    aws_byte_buf_clean_up(&serialized_diff);

    return AWS_OP_SUCCESS;
}

/* clang-format off */
static struct bigint_arithmetic_test s_subtract_zero_test_cases[] = {
    {
        .value1 =       "0x00",
        .value2 =          "0",
        .expected_result = "0",
    },
    {
        .value1 =         "0x111122223333445566789aaaaabbbbbbcccccddddddeeeeef",
        .value2 =                                                           "0",
        .expected_result = "-111122223333445566789aaaaabbbbbbcccccddddddeeeeef",
        .is_negative1 = true,
    },
    {
        .value1 =        "0xabcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef012",
        .value2 =                                                                                                  "0",
        .expected_result = "abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef012",
    },
};
/* clang-format on */

static int s_test_bigint_subtract_zero(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_subtraction_test(allocator, s_subtract_zero_test_cases, AWS_ARRAY_SIZE(s_subtract_zero_test_cases));
}

AWS_TEST_CASE(test_bigint_subtract_zero, s_test_bigint_subtract_zero)

/* clang-format off */
static struct bigint_arithmetic_test s_subtract_positive_result_test_cases[] = {
    {
        .value1 =       "0x06",
        .value2 =          "1",
        .expected_result = "5",
    },
    {
        .value1 =       "0x01",
        .value2 =          "6",
        .expected_result = "7",
        .is_negative2 = true,
    },
    {
        .value1 =       "0x01",
        .value2 =          "6",
        .expected_result = "5",
        .is_negative1 = true,
        .is_negative2 = true,
    },
    {
        .value1 =        "0x345634563456789876543456789",
        .value2 =          "111111112222222333333332222",
        .expected_result = "234523451234567543210124567",
    },
    {
        .value1 =        "0x111111111111111111111111111111111111111111111111111111111111111",
        .value2 =           "23456789123456789123456789123456789123456789123456789123456789",
        .expected_result =  "edcba987fedcba987fedcba987fedcba987fedcba987fedcba987fedcba988",
    },
    {
        .value1 =        "0x10000000000000000000000000000000000000000000000000000000000000000",
        .value2 =                                                                          "1",
        .expected_result =  "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
    },
};
/* clang-format on */

static int s_test_bigint_subtract_positive_result(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_subtraction_test(
        allocator, s_subtract_positive_result_test_cases, AWS_ARRAY_SIZE(s_subtract_positive_result_test_cases));
}

AWS_TEST_CASE(test_bigint_subtract_positive_result, s_test_bigint_subtract_positive_result)

/* clang-format off */
static struct bigint_arithmetic_test s_subtract_negative_result_test_cases[] = {
    {
        .value1 =                "0x00",
        .value2 =           "fffffffff",
        .expected_result = "-fffffffff",
    },
    {
        .value1 =         "0xaaaaaaaaaaa",
        .value2 =           "bbbbbbbbbbb",
        .expected_result = "-11111111111",
    },
    {
        .value1 =         "0x123123123123123",
        .value2 =           "321321321321321",
        .expected_result = "-444444444444444",
        .is_negative1 = true,
    },
    {
        .value1 =         "0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        .value2 =           "5454545454545454545454545454545",
        .expected_result = "-5656565656565656565656565656565",
        .is_negative1 = true,
        .is_negative2 = true,
    },
};
/* clang-format on */

static int s_test_bigint_subtract_negative_result(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_subtraction_test(
        allocator, s_subtract_negative_result_test_cases, AWS_ARRAY_SIZE(s_subtract_negative_result_test_cases));
}

AWS_TEST_CASE(test_bigint_subtract_negative_result, s_test_bigint_subtract_negative_result)

/*
 * Tests (val1 x val2 ) against expected result
 * Tests (-val1 x val2), (val1 x -val2), (-val1 x -val2) against +/-(val1 x val2)
 * Tests (val2 x val1), (-val2 x val1), (val2 x -val1), (-val2 x -val1) against +/-(val1 x val2)
 * Tests aliased multiplication
 */
static int s_do_multiplication_test(
    struct aws_allocator *allocator,
    struct bigint_arithmetic_test *test_cases,
    size_t test_case_count) {

    struct aws_byte_buf serialized_product;
    aws_byte_buf_init(&serialized_product, allocator, 0);

    for (size_t i = 0; i < test_case_count; ++i) {
        struct aws_bigint value1;
        struct aws_bigint value2;

        struct bigint_arithmetic_test *testcase = &test_cases[i];

        /* init operands */
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value2, allocator, aws_byte_cursor_from_c_str(testcase->value2)));
        if (testcase->is_negative2) {
            aws_bigint_negate(&value2);
        }

        /* test val1 x val2 */
        struct aws_bigint product;
        aws_bigint_init_from_uint64(&product, allocator, 0);

        ASSERT_SUCCESS(aws_bigint_multiply(&product, &value1, &value2));

        serialized_product.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&product, &serialized_product));

        size_t expected_length = strlen(testcase->expected_result);
        ASSERT_TRUE(serialized_product.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(
            testcase->expected_result, expected_length, serialized_product.buffer, serialized_product.len);

        struct aws_bigint negated_product;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&negated_product, &product));
        aws_bigint_negate(&negated_product);

        /* test val2 x val1 */
        struct aws_bigint result;
        aws_bigint_init_from_uint64(&result, allocator, 0);

        ASSERT_SUCCESS(aws_bigint_multiply(&result, &value2, &value1));
        ASSERT_TRUE(aws_bigint_equals(&result, &product));

        /* aliasing tests*/

        /* test val1 *= val2 */
        struct aws_bigint value1_copy;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&value1_copy, &value1));

        ASSERT_SUCCESS(aws_bigint_multiply(&value1_copy, &value1_copy, &value2));
        ASSERT_TRUE(aws_bigint_equals(&value1_copy, &product));

        /* test val2 *= val1 */
        struct aws_bigint value2_copy;
        ASSERT_SUCCESS(aws_bigint_init_from_copy(&value2_copy, &value2));

        ASSERT_SUCCESS(aws_bigint_multiply(&value2_copy, &value1, &value2_copy));
        ASSERT_TRUE(aws_bigint_equals(&value2_copy, &product));

        /* negation tests */
        aws_bigint_negate(&value1);

        /* test -val1 x val2 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value1, &value2);
        ASSERT_TRUE(aws_bigint_equals(&result, &negated_product));

        /* test val2 x -val1 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value2, &value1);
        ASSERT_TRUE(aws_bigint_equals(&result, &negated_product));

        aws_bigint_negate(&value2);

        /* test -val1 x -val2 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value1, &value2);
        ASSERT_TRUE(aws_bigint_equals(&result, &product));

        /* test -val2 x -val1 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value2, &value1);
        ASSERT_TRUE(aws_bigint_equals(&result, &product));

        aws_bigint_negate(&value1);

        /* test val1 x -val2 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value1, &value2);
        ASSERT_TRUE(aws_bigint_equals(&result, &negated_product));

        /* test -val2 x val1 */
        aws_bigint_clean_up(&result);
        aws_bigint_init_from_uint64(&result, allocator, 0);

        aws_bigint_multiply(&result, &value2, &value1);
        ASSERT_TRUE(aws_bigint_equals(&result, &negated_product));

        aws_bigint_clean_up(&value1_copy);
        aws_bigint_clean_up(&value2_copy);
        aws_bigint_clean_up(&result);
        aws_bigint_clean_up(&negated_product);
        aws_bigint_clean_up(&product);
        aws_bigint_clean_up(&value2);
        aws_bigint_clean_up(&value1);
    }

    aws_byte_buf_clean_up(&serialized_product);

    return AWS_OP_SUCCESS;
}

static struct bigint_arithmetic_test s_multiply_one_and_zero_test_cases[] = {
    {
        .value1 = "0x00",
        .value2 = "0",
        .expected_result = "0",
    },
    {
        .value1 = "0x00",
        .value2 = "15",
        .expected_result = "0",
    },
    {
        .value1 = "19578923468972567982384578923547abcdeffffffffffffffffffff",
        .value2 = "0x00",
        .expected_result = "0",
    },
    {
        .value1 = "0x01",
        .value2 = "1",
        .expected_result = "1",
    },
    {
        .value1 = "0x0123457698badceffedbc467825354298badceffedbc4678253542",
        .value2 = "1",
        .expected_result = "123457698badceffedbc467825354298badceffedbc4678253542",
    },
    {
        .value1 = "0x5278967893465879032467094302895678ababdf5789345795",
        .value2 = "1",
        .expected_result = "5278967893465879032467094302895678ababdf5789345795",
        .is_negative1 = true,
        .is_negative2 = true,
    },
};

static int s_test_bigint_multiply_one_and_zero(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_multiplication_test(
        allocator, s_multiply_one_and_zero_test_cases, AWS_ARRAY_SIZE(s_multiply_one_and_zero_test_cases));
}

AWS_TEST_CASE(test_bigint_multiply_one_and_zero, s_test_bigint_multiply_one_and_zero)

static struct bigint_arithmetic_test s_multiply_test_cases[] = {
    {
        .value1 = "0x02",
        .value2 = "2",
        .expected_result = "4",
    },
    {
        .value1 = "0x02",
        .value2 = "80000000",
        .expected_result = "100000000",
    },
    {
        .value1 = "ffffffff",
        .value2 = "ffffffff",
        .expected_result = "fffffffe00000001",
    },
    {
        .value1 = "ffffffffffffffff",
        .value2 = "ffffffffffffffff",
        .expected_result = "fffffffffffffffe0000000000000001",
    },
    {
        .value1 = "ffffffffffffffffffffffff",
        .value2 = "ffffffffffffffffffffffff",
        .expected_result = "fffffffffffffffffffffffe000000000000000000000001",
    },
    {
        .value1 = "789abcdef789abcdef789abcdef789abcdef789abcdef789abcdef",
        .value2 = "1234565432100000000000000000000000000000056af563",
        .expected_result =
            "8938961b08098ec33d7098ec33d7098ec33d7099150a6cde2acd04b1aa16b54ba49c09c7ca49c09c7ca49c09c7ca4997c5e6d",
    },
};

static int s_test_bigint_multiply(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_multiplication_test(allocator, s_multiply_test_cases, AWS_ARRAY_SIZE(s_multiply_test_cases));
}

AWS_TEST_CASE(test_bigint_multiply, s_test_bigint_multiply)

struct aws_bigint_shift_test {
    const char *value1;
    const char *expected_result;
    size_t shift_amount;
    bool is_negative1;
};

static int s_do_right_shift_test(
    struct aws_allocator *allocator,
    struct aws_bigint_shift_test *test_cases,
    size_t test_case_count) {

    struct aws_byte_buf serialized_shift;
    aws_byte_buf_init(&serialized_shift, allocator, 0);

    for (size_t i = 0; i < test_case_count; ++i) {
        struct aws_bigint value1;
        struct aws_bigint_shift_test *testcase = &test_cases[i];

        /* init operands */
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }

        aws_bigint_shift_right(&value1, testcase->shift_amount);

        serialized_shift.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&value1, &serialized_shift));

        size_t expected_length = strlen(testcase->expected_result);
        ASSERT_TRUE(serialized_shift.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(
            testcase->expected_result, expected_length, serialized_shift.buffer, serialized_shift.len);

        aws_bigint_clean_up(&value1);
    }

    aws_byte_buf_clean_up(&serialized_shift);

    return AWS_OP_SUCCESS;
}

static struct aws_bigint_shift_test s_shift_right_test_cases[] = {
    {
        .value1 = "0x00",
        .expected_result = "0",
        .shift_amount = 0,
    },
    {
        .value1 = "0xFF",
        .expected_result = "ff",
        .shift_amount = 0,
    },
    {
        .value1 = "0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210",
        .expected_result = "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210",
        .shift_amount = 0,
    },
    {
        .value1 = "0x02",
        .expected_result = "1",
        .shift_amount = 1,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "3fbfbfbf",
        .shift_amount = 1,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "7f7f7f7",
        .shift_amount = 4,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "7f7f7",
        .shift_amount = 12,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "7",
        .shift_amount = 28,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "1",
        .shift_amount = 30,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "0",
        .shift_amount = 31,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "0",
        .shift_amount = 32,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "0",
        .shift_amount = 128,
    },
    {
        .value1 = "0x7f7f7f7f",
        .expected_result = "0",
        .shift_amount = 65537,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "421084210842108",
        .shift_amount = 1,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "210842108421084",
        .shift_amount = 2,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "108421084210842",
        .shift_amount = 3,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "10842108",
        .shift_amount = 31,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "8421084",
        .shift_amount = 32,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "4210842",
        .shift_amount = 33,
    },
    {
        .value1 = "0x842108421084210",
        .expected_result = "2108421",
        .shift_amount = 34,
    },
    {
        .value1 = "0x842108421084210842108421",
        .expected_result = "8421084210842108",
        .shift_amount = 32,
    },
    {
        .value1 = "0x842108421084210842108421",
        .expected_result = "84210842",
        .shift_amount = 64,
    },
    {
        .value1 = "0x842108421084210842108421",
        .expected_result = "42108421",
        .shift_amount = 65,
    },
    {
        .value1 = "0x842108421084210842108421",
        .expected_result = "21084210",
        .shift_amount = 66,
    },
    {
        .value1 = "0x842108421084210842108421",
        .expected_result = "10842108",
        .shift_amount = 67,
    },
};

static int s_test_bigint_right_shift(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_right_shift_test(allocator, s_shift_right_test_cases, AWS_ARRAY_SIZE(s_shift_right_test_cases));
}

AWS_TEST_CASE(test_bigint_right_shift, s_test_bigint_right_shift)

static int s_do_left_shift_test(
    struct aws_allocator *allocator,
    struct aws_bigint_shift_test *test_cases,
    size_t test_case_count) {

    struct aws_byte_buf serialized_shift;
    aws_byte_buf_init(&serialized_shift, allocator, 0);

    for (size_t i = 0; i < test_case_count; ++i) {
        struct aws_bigint value1;
        struct aws_bigint_shift_test *testcase = &test_cases[i];

        /* init operands */
        ASSERT_SUCCESS(aws_bigint_init_from_hex(&value1, allocator, aws_byte_cursor_from_c_str(testcase->value1)));
        if (testcase->is_negative1) {
            aws_bigint_negate(&value1);
        }

        aws_bigint_shift_left(&value1, testcase->shift_amount);

        serialized_shift.len = 0;
        ASSERT_SUCCESS(aws_bigint_bytebuf_debug_output(&value1, &serialized_shift));

        size_t expected_length = strlen(testcase->expected_result);
        ASSERT_TRUE(serialized_shift.len == expected_length);
        ASSERT_BIN_ARRAYS_EQUALS(
            testcase->expected_result, expected_length, serialized_shift.buffer, serialized_shift.len);

        aws_bigint_clean_up(&value1);
    }

    aws_byte_buf_clean_up(&serialized_shift);

    return AWS_OP_SUCCESS;
}

static struct aws_bigint_shift_test s_shift_left_test_cases[] = {
    {
        .value1 = "0x00",
        .expected_result = "0",
        .shift_amount = 0,
    },
    {
        .value1 = "0x1F",
        .expected_result = "1f",
        .shift_amount = 0,
    },
    {
        .value1 = "0xfedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210",
        .expected_result = "fedcba9876543210fedcba9876543210fedcba9876543210fedcba9876543210",
        .shift_amount = 0,
    },
    {
        .value1 = "0x01",
        .expected_result = "2",
        .shift_amount = 1,
    },
    {
        .value1 = "0x01",
        .expected_result = "80000000",
        .shift_amount = 31,
    },
    {
        .value1 = "0x01",
        .expected_result = "10000000000000000",
        .shift_amount = 64,
    },
    {
        .value1 = "0x01",
        .expected_result = "20000000000000000",
        .shift_amount = 65,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "108421084210842108420",
        .shift_amount = 1,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "210842108421084210840",
        .shift_amount = 2,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "4210842108421084210800000000",
        .shift_amount = 31,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "8421084210842108421000000000",
        .shift_amount = 32,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "842108421084210842100000000000000000",
        .shift_amount = 64,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "84210842108421084210000000000000000000000000",
        .shift_amount = 96,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "108421084210842108420000000000000000000000000",
        .shift_amount = 97,
    },
    {
        .value1 = "0x84210842108421084210",
        .expected_result = "4210842108421084210800000000000000000000000000000000",
        .shift_amount = 127,
    },
};

static int s_test_bigint_left_shift(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    return s_do_left_shift_test(allocator, s_shift_left_test_cases, AWS_ARRAY_SIZE(s_shift_left_test_cases));
}

AWS_TEST_CASE(test_bigint_left_shift, s_test_bigint_left_shift)