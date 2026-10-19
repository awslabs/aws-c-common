/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bignum.h>

#include <aws/testing/aws_test_harness.h>

#include <string.h>

struct big_str_case {
    const char *input;
    const char *expected;
};

// Asserts that a pointer-returning constructor failed with the given error.
#define ASSERT_NEW_FAILS(error, expression, ...)                                                                       \
    do {                                                                                                               \
        aws_reset_error();                                                                                             \
        void *assert_new_result = (expression);                                                                        \
        ASSERT_NULL(assert_new_result, __VA_ARGS__);                                                                   \
        ASSERT_INT_EQUALS((error), aws_last_error(), __VA_ARGS__);                                                     \
    } while (0)

static int s_check_magnitude_equals(
    const struct aws_big_integer *a,
    const struct aws_big_integer *b,
    struct aws_allocator *allocator) {

    struct aws_byte_buf a_bytes;
    struct aws_byte_buf b_bytes;
    ASSERT_SUCCESS(aws_byte_buf_init(&a_bytes, allocator, 1));
    ASSERT_SUCCESS(aws_byte_buf_init(&b_bytes, allocator, 1));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(a, &a_bytes));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(b, &b_bytes));
    ASSERT_TRUE(aws_byte_buf_eq(&a_bytes, &b_bytes));
    ASSERT_INT_EQUALS(aws_big_integer_get_sign(a), aws_big_integer_get_sign(b));
    aws_byte_buf_clean_up(&a_bytes);
    aws_byte_buf_clean_up(&b_bytes);
    return AWS_OP_SUCCESS;
}

static int s_check_big_integer_round_trip(struct aws_allocator *allocator, const char *input, const char *expected) {
    struct aws_big_integer *v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(input));
    ASSERT_NOT_NULL(v, "input: %s", input);

    struct aws_byte_buf out;
    ASSERT_SUCCESS(aws_byte_buf_init(&out, allocator, 1));
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&out, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&out), expected, "input: %s", input);

    struct aws_big_integer *reparsed = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&out));
    ASSERT_NOT_NULL(reparsed);
    ASSERT_SUCCESS(s_check_magnitude_equals(v, reparsed, allocator));

    aws_big_integer_destroy(reparsed);
    aws_byte_buf_clean_up(&out);
    aws_big_integer_destroy(v);
    return AWS_OP_SUCCESS;
}

static int s_big_integer_round_trip_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct big_str_case cases[] = {
        {"0", "0"},
        {"-0", "0"},
        {"+0", "0"},
        {"00", "0"},
        {"0000", "0"},
        {"-00", "0"},
        {"01", "1"},
        {"-01", "-1"},
        {"1", "1"},
        {"+42", "42"},
        {"-42", "-42"},
        {"18446744073709551616", "18446744073709551616"},
        {"-123456789012345678901234567890123456789012345678901234567890",
         "-123456789012345678901234567890123456789012345678901234567890"},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        ASSERT_SUCCESS(s_check_big_integer_round_trip(allocator, cases[i].input, cases[i].expected));
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_round_trip, s_big_integer_round_trip_fn)

static int s_big_integer_representation_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_big_integer *v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-120"));
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(v));
    uint8_t expected_120[] = {120};
    uint8_t storage[16];
    struct aws_byte_buf out = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(v, &out));
    ASSERT_BIN_ARRAYS_EQUALS(expected_120, sizeof(expected_120), out.buffer, out.len);
    aws_big_integer_destroy(v);

    // negative zero does not exist
    v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-0"));
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(v));
    out = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(v, &out));
    ASSERT_UINT_EQUALS(0, out.len);
    aws_big_integer_destroy(v);

    static const uint8_t zero_bytes[] = {0x00, 0x00};
    v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(zero_bytes, sizeof(zero_bytes)), false);
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(v));
    aws_big_integer_destroy(v);

    v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(NULL, 0), false);
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(v));
    aws_big_integer_destroy(v);

    // zero is never negative, whatever the caller asks for
    v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(zero_bytes, sizeof(zero_bytes)), true);
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(v));
    aws_big_integer_destroy(v);

    v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(NULL, 0), true);
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(v));
    struct aws_big_integer *zero = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("0"));
    ASSERT_NOT_NULL(zero);
    ASSERT_TRUE(aws_big_integer_eq(zero, v));
    aws_big_integer_destroy(zero);
    aws_big_integer_destroy(v);

    // is_negative sets the sign of a nonzero magnitude
    static const uint8_t one_hundred[] = {0x00, 0x64};
    v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(one_hundred, sizeof(one_hundred)), true);
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(v));
    out = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(v, &out));
    ASSERT_UINT_EQUALS(1, out.len);
    ASSERT_UINT_EQUALS(0x64, out.buffer[0]);
    struct aws_big_integer *expected = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-100"));
    ASSERT_NOT_NULL(expected);
    ASSERT_TRUE(aws_big_integer_eq(expected, v));
    aws_big_integer_destroy(expected);
    aws_big_integer_destroy(v);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_representation, s_big_integer_representation_fn)

static int s_big_integer_parse_invalid_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *cases[] = {
        "",
        "-",
        "+",
        "--1",
        "+-1",
        "-+1",
        "1a",
        "a1",
        " 1",
        "1 ",
        "1.0",
        "1e3",
        "0x10",
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        ASSERT_NEW_FAILS(
            AWS_ERROR_INVALID_ARGUMENT,
            aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i])),
            "input: %s",
            cases[i]);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_parse_invalid, s_big_integer_parse_invalid_fn)

static int s_big_integer_to_str_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_big_integer *v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-12345"));
    ASSERT_NOT_NULL(v);

    // appends to existing content
    struct aws_byte_buf dynamic;
    ASSERT_SUCCESS(aws_byte_buf_init_copy_from_cursor(&dynamic, allocator, aws_byte_cursor_from_c_str("n=")));
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&dynamic, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&dynamic), "n=-12345");
    aws_byte_buf_clean_up(&dynamic);

    // fixed buffer that is one byte short is left untouched
    uint8_t storage[6];
    struct aws_byte_buf fixed = aws_byte_buf_from_empty_array(storage, 5);
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append_big_integer(&fixed, v));
    ASSERT_UINT_EQUALS(0, fixed.len);

    fixed = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&fixed, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&fixed), "-12345");

    aws_big_integer_destroy(v);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_to_str_buffer, s_big_integer_to_str_buffer_fn)

// Checks to_str of `v` into a growable buffer, an exact-fit fixed buffer, and a fixed buffer one byte short.
static int s_check_to_str_all_buffers(struct aws_allocator *allocator, const struct aws_big_integer *v) {
    struct aws_byte_buf grown;
    ASSERT_SUCCESS(aws_byte_buf_init(&grown, allocator, 0));
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&grown, v));

    size_t len = grown.len;

    // The bound is never short, and is at most one byte over.
    size_t max_strlen = aws_big_integer_max_strlen(v);
    ASSERT_TRUE(max_strlen >= len);
    ASSERT_TRUE(max_strlen <= len + 1);

    struct aws_byte_buf fixed;
    ASSERT_SUCCESS(aws_byte_buf_init(&fixed, allocator, len + 1));
    fixed.allocator = NULL;
    fixed.capacity = len;
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&fixed, v));
    ASSERT_TRUE(aws_byte_buf_eq(&grown, &fixed));
    uint8_t *fixed_storage = fixed.buffer;
    fixed.capacity = len - 1;
    fixed.len = 0;
    if (fixed.capacity == 0) {
        // a zero capacity byte buf with a non-NULL buffer is not a valid byte buf
        fixed.buffer = NULL;
    }
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append_big_integer(&fixed, v));
    ASSERT_UINT_EQUALS(0, fixed.len);
    aws_mem_release(allocator, fixed_storage);

    // The output parses back to the same value.
    struct aws_big_integer *parsed = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&grown));
    ASSERT_NOT_NULL(parsed);
    ASSERT_TRUE(aws_big_integer_eq(v, parsed));
    aws_big_integer_destroy(parsed);
    aws_byte_buf_clean_up(&grown);
    return AWS_OP_SUCCESS;
}

// The digit count bound used to size the output must be tight enough that exact-fit buffers always work. Powers of
// two and of ten, and the values just below them, are where an off by one in the bound would show.
static int s_big_integer_to_str_exact_fit_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    for (size_t digits = 1; digits <= 4932; digits += (digits < 100 ? 1 : 350)) {
        char *text = aws_mem_acquire(allocator, digits + 2);
        ASSERT_NOT_NULL(text);

        for (int negative = 0; negative < 2; ++negative) {
            char *start = text + 1;
            size_t total = digits;
            if (negative) {
                *--start = '-';
                ++total;
            }

            // 10^(digits-1)
            start[negative ? 1 : 0] = '1';
            memset(start + (negative ? 2 : 1), '0', digits - 1);
            struct aws_big_integer *v =
                aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_array(start, total));
            ASSERT_NOT_NULL(v);
            ASSERT_SUCCESS(s_check_to_str_all_buffers(allocator, v));
            aws_big_integer_destroy(v);

            // 10^digits - 1
            memset(start + (negative ? 1 : 0), '9', digits);
            v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_array(start, total));
            ASSERT_NOT_NULL(v);
            ASSERT_SUCCESS(s_check_to_str_all_buffers(allocator, v));
            aws_big_integer_destroy(v);
        }

        aws_mem_release(allocator, text);
    }

    // 2^k and 2^k - 1 for every bit length that touches a word boundary, and the largest accepted value.
    uint8_t *bytes = aws_mem_acquire(allocator, 2048);
    ASSERT_NOT_NULL(bytes);
    for (size_t len = 1; len <= 2048; len += (len < 40 ? 1 : 255)) {
        for (int power_of_two = 0; power_of_two < 2; ++power_of_two) {
            if (power_of_two) {
                memset(bytes, 0, len);
                bytes[0] = 0x80;
            } else {
                memset(bytes, 0xff, len);
            }
            struct aws_big_integer *v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, len), false);
            ASSERT_NOT_NULL(v);
            ASSERT_SUCCESS(s_check_to_str_all_buffers(allocator, v));
            aws_big_integer_destroy(v);
        }
    }
    memset(bytes, 0xff, 2048);
    struct aws_big_integer *largest = aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, 2048), false);
    ASSERT_NOT_NULL(largest);
    ASSERT_SUCCESS(s_check_to_str_all_buffers(allocator, largest));
    aws_big_integer_destroy(largest);
    aws_mem_release(allocator, bytes);

    struct aws_big_integer *zero = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("0"));
    ASSERT_NOT_NULL(zero);
    ASSERT_SUCCESS(s_check_to_str_all_buffers(allocator, zero));
    aws_big_integer_destroy(zero);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_to_str_exact_fit, s_big_integer_to_str_exact_fit_fn)

struct magnitude_case {
    const char *decimal;
    const uint8_t *bytes;
    size_t bytes_len;
};

static int s_big_integer_magnitude_vectors_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    static const uint8_t one_e19[] = {0x8a, 0xc7, 0x23, 0x04, 0x89, 0xe8, 0x00, 0x00};
    static const uint8_t one_e38[] = {
        0x4b, 0x3b, 0x4c, 0xa8, 0x5a, 0x86, 0xc4, 0x7a, 0x09, 0x8a, 0x22, 0x40, 0x00, 0x00, 0x00, 0x00};
    static const uint8_t one_e57[] = {0x28, 0xc8, 0x7c, 0xb5, 0xc8, 0x9a, 0x25, 0x71, 0xeb, 0xfd, 0xcb, 0x54,
                                      0x86, 0x4a, 0xda, 0x83, 0x4a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
    static const uint8_t two_64[] = {0x01, 0, 0, 0, 0, 0, 0, 0, 0};
    static const uint8_t two_64_minus_1[] = {0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff};
    static const uint8_t two_128[] = {0x01, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
    static const uint8_t mixed[] = {0x01, 0x8e, 0xe9, 0x0f, 0xf6, 0xc3, 0x73, 0xe0, 0xee, 0x4e, 0x3f, 0x0a, 0xd2};

    struct magnitude_case cases[] = {
        {"10000000000000000000", one_e19, sizeof(one_e19)},
        {"100000000000000000000000000000000000000", one_e38, sizeof(one_e38)},
        {"1000000000000000000000000000000000000000000000000000000000", one_e57, sizeof(one_e57)},
        {"18446744073709551616", two_64, sizeof(two_64)},
        {"18446744073709551615", two_64_minus_1, sizeof(two_64_minus_1)},
        {"340282366920938463463374607431768211456", two_128, sizeof(two_128)},
        {"123456789012345678901234567890", mixed, sizeof(mixed)},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        const struct magnitude_case *c = &cases[i];

        // decimal -> words -> bytes
        struct aws_big_integer *v = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(c->decimal));
        ASSERT_NOT_NULL(v, "case %zu", i);
        struct aws_byte_buf bytes;
        ASSERT_SUCCESS(aws_byte_buf_init(&bytes, allocator, 1));
        ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(v, &bytes));
        ASSERT_BIN_ARRAYS_EQUALS(c->bytes, c->bytes_len, bytes.buffer, bytes.len, "case %zu", i);
        aws_byte_buf_clean_up(&bytes);
        aws_big_integer_destroy(v);

        // bytes (with and without redundant leading zeros) -> words -> decimal
        for (size_t pad = 0; pad < 2; ++pad) {
            uint8_t padded[64] = {0};
            memcpy(padded + pad * 3, c->bytes, c->bytes_len);
            struct aws_byte_cursor magnitude = aws_byte_cursor_from_array(padded, pad * 3 + c->bytes_len);

            v = aws_big_integer_new(allocator, magnitude, false);
            ASSERT_NOT_NULL(v, "case %zu", i);
            ASSERT_TRUE(aws_big_integer_get_sign(v) >= 0);

            struct aws_byte_buf str;
            ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 1));
            ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&str, v));
            ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), c->decimal, "case %zu", i);
            aws_byte_buf_clean_up(&str);
            aws_big_integer_destroy(v);

            // the same bytes with is_negative give the negated value
            v = aws_big_integer_new(allocator, magnitude, true);
            ASSERT_NOT_NULL(v, "case %zu", i);
            ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(v));

            ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 1));
            ASSERT_SUCCESS(aws_byte_buf_append_byte_dynamic(&str, '-'));
            ASSERT_SUCCESS(aws_byte_buf_append_dynamic(
                &str, &(struct aws_byte_cursor){.ptr = (uint8_t *)c->decimal, .len = strlen(c->decimal)}));
            struct aws_big_integer *expected =
                aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&str));
            ASSERT_NOT_NULL(expected, "case %zu", i);
            ASSERT_TRUE(aws_big_integer_eq(expected, v), "case %zu", i);
            aws_big_integer_destroy(expected);
            aws_byte_buf_clean_up(&str);
            aws_big_integer_destroy(v);
        }
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_magnitude_vectors, s_big_integer_magnitude_vectors_fn)

// Powers of ten and their predecessors straddle every 9-digit chunk and 32-bit word boundary.
static int s_big_integer_digit_boundaries_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    char input[256];
    for (size_t digits = 1; digits <= 200; ++digits) {
        input[0] = '1';
        memset(input + 1, '0', digits);
        input[digits + 1] = '\0';
        ASSERT_SUCCESS(s_check_big_integer_round_trip(allocator, input, input), "10^%zu", digits);

        memset(input, '9', digits);
        input[digits] = '\0';
        ASSERT_SUCCESS(s_check_big_integer_round_trip(allocator, input, input), "10^%zu - 1", digits);

        input[0] = '-';
        memset(input + 1, '9', digits);
        input[digits + 1] = '\0';
        ASSERT_SUCCESS(s_check_big_integer_round_trip(allocator, input, input), "-(10^%zu - 1)", digits);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_digit_boundaries, s_big_integer_digit_boundaries_fn)

// bytes -> words -> decimal -> words -> bytes must be the identity for every length and byte pattern.
static int s_big_integer_magnitude_round_trip_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    uint8_t bytes[300];
    for (size_t len = 1; len <= sizeof(bytes); ++len) {
        for (int pattern = 0; pattern < 3; ++pattern) {
            for (size_t i = 0; i < len; ++i) {
                switch (pattern) {
                    case 0:
                        bytes[i] = (uint8_t)(i * 131 + 7);
                        break;
                    case 1:
                        bytes[i] = 0xff;
                        break;
                    default:
                        bytes[i] = i == 0 ? 0x80 : 0x00;
                        break;
                }
            }
            if (bytes[0] == 0) {
                bytes[0] = 1;
            }

            struct aws_big_integer *from_bytes =
                aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, len), false);
            ASSERT_NOT_NULL(from_bytes);

            struct aws_byte_buf str;
            ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 1));
            ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&str, from_bytes));

            struct aws_big_integer *from_str =
                aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&str));
            ASSERT_NOT_NULL(from_str);

            struct aws_byte_buf round_tripped;
            ASSERT_SUCCESS(aws_byte_buf_init(&round_tripped, allocator, 1));
            ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(from_str, &round_tripped));
            ASSERT_BIN_ARRAYS_EQUALS(
                bytes, len, round_tripped.buffer, round_tripped.len, "len %zu pattern %d", len, pattern);

            aws_byte_buf_clean_up(&round_tripped);
            aws_big_integer_destroy(from_str);
            aws_byte_buf_clean_up(&str);
            aws_big_integer_destroy(from_bytes);
        }
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_magnitude_round_trip, s_big_integer_magnitude_round_trip_fn)

static int s_big_integer_magnitude_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    uint8_t bytes[] = {0x01, 0x02, 0x03};
    struct aws_big_integer *v = aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, sizeof(bytes)), false);
    ASSERT_NOT_NULL(v);

    uint8_t storage[3];
    struct aws_byte_buf fixed = aws_byte_buf_from_empty_array(storage, 2);
    ASSERT_ERROR(AWS_ERROR_DEST_COPY_TOO_SMALL, aws_big_integer_get_magnitude_be(v, &fixed));
    ASSERT_UINT_EQUALS(0, fixed.len);

    fixed = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(v, &fixed));
    ASSERT_BIN_ARRAYS_EQUALS(bytes, sizeof(bytes), fixed.buffer, fixed.len);

    aws_big_integer_destroy(v);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_magnitude_buffer, s_big_integer_magnitude_buffer_fn)

static int s_check_big_decimal_round_trip(struct aws_allocator *allocator, const char *input, const char *expected) {
    struct aws_big_decimal *v = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(input));
    ASSERT_NOT_NULL(v, "input: %s", input);

    struct aws_byte_buf out;
    ASSERT_SUCCESS(aws_byte_buf_init(&out, allocator, 1));
    ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&out, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&out), expected, "input: %s", input);

    struct aws_big_decimal *reparsed = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_buf(&out));
    ASSERT_NOT_NULL(reparsed);
    ASSERT_SUCCESS(
        s_check_magnitude_equals(aws_big_decimal_get_mantissa(v), aws_big_decimal_get_mantissa(reparsed), allocator),
        "input: %s",
        input);
    ASSERT_INT_EQUALS(aws_big_decimal_get_exponent(v), aws_big_decimal_get_exponent(reparsed), "input: %s", input);

    aws_big_decimal_destroy(reparsed);
    aws_byte_buf_clean_up(&out);
    aws_big_decimal_destroy(v);
    return AWS_OP_SUCCESS;
}

static int s_big_decimal_round_trip_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct big_str_case cases[] = {
        {"0", "0e0"},
        {"-0", "0e0"},
        {"-0.00", "0e-2"},
        {"+0", "0e0"},
        {"+1.0", "10e-1"},
        {"00", "0e0"},
        {"-00", "0e0"},
        {"00.1", "1e-1"},
        {"01", "1e0"},
        {"01.0", "10e-1"},
        {"-01.0", "-10e-1"},
        {"123", "123e0"},
        {"-123", "-123e0"},
        {"0.0", "0e-1"},
        {"1.50", "150e-2"},
        {"-0.5", "-5e-1"},
        {"0.0012", "12e-4"},
        {"0.000001", "1e-6"},
        {"0.0000001", "1e-7"},
        {"-0.00000012", "-12e-8"},
        {"0.0000010", "10e-7"},
        {"123.45e2", "12345e0"},
        {"123.45E-2", "12345e-4"},
        {"1e3", "1e3"},
        {"1e+3", "1e3"},
        {"1.23e3", "123e1"},
        {"-12.3e5", "-123e4"},
        {"0e5", "0e5"},
        {"0e-10", "0e-10"},
        {"1E-9", "1e-9"},
        {"1e-0", "1e0"},
        {"1e00000000000000000000000000003", "1e3"},
        {"12345678901234567890.123456789", "12345678901234567890123456789e-9"},
        {"1e9223372036854775807", "1e9223372036854775807"},
        {"10e9223372036854775807", "10e9223372036854775807"},
        {"1e-9223372036854775808", "1e-9223372036854775808"},
        {"1.0e-9223372036854775807", "10e-9223372036854775808"},
        // a 9-digit chunk boundary falls inside the fractional part
        {"123456789012345678.9012345678901234567", "1234567890123456789012345678901234567e-19"},
        {"0.00000000000000000001", "1e-20"},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        ASSERT_SUCCESS(s_check_big_decimal_round_trip(allocator, cases[i].input, cases[i].expected));
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_decimal_round_trip, s_big_decimal_round_trip_fn)

static int s_big_decimal_representation_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_big_decimal *v = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-1.50"));
    ASSERT_NOT_NULL(v);
    const struct aws_big_integer *mantissa = aws_big_decimal_get_mantissa(v);
    uint8_t expected_150[] = {150};
    uint8_t storage[16];
    struct aws_byte_buf out = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(mantissa, &out));
    ASSERT_BIN_ARRAYS_EQUALS(expected_150, sizeof(expected_150), out.buffer, out.len);
    ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(mantissa));
    ASSERT_INT_EQUALS(-2, aws_big_decimal_get_exponent(v));
    aws_big_decimal_destroy(v);

    v = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("0.0012e10"));
    ASSERT_NOT_NULL(v);
    mantissa = aws_big_decimal_get_mantissa(v);
    uint8_t expected_12[] = {12};
    out = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(mantissa, &out));
    ASSERT_BIN_ARRAYS_EQUALS(expected_12, sizeof(expected_12), out.buffer, out.len);
    ASSERT_TRUE(aws_big_integer_get_sign(mantissa) >= 0);
    ASSERT_INT_EQUALS(6, aws_big_decimal_get_exponent(v));
    aws_big_decimal_destroy(v);

    // scale is preserved on a zero mantissa, which is never negative
    v = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-0.00"));
    ASSERT_NOT_NULL(v);
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(aws_big_decimal_get_mantissa(v)));
    ASSERT_INT_EQUALS(-2, aws_big_decimal_get_exponent(v));
    aws_big_decimal_destroy(v);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_decimal_representation, s_big_decimal_representation_fn)

static int s_big_decimal_parse_invalid_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *cases[] = {
        "",     ".",        "-",     "+",   "-.",  ".0",  "-.0",   "0.",    "1.",
        "-1.",  "e5",       ".e5",   "1e",  "1e+", "1e-", "1e+-5", "1e--5", "1e++5",
        "1ee2", "1e2.5",    "1.2.3", "+-1", " 1",  "1 ",  "1e5x",  "1e-+5", "1e99999999999999999999x",
        "NaN",  "Infinity",
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        ASSERT_NEW_FAILS(
            AWS_ERROR_INVALID_ARGUMENT,
            aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i])),
            "input: %s",
            cases[i]);
    }

    const char *overflow_cases[] = {
        // exponent does not fit in int64_t
        "1e9223372036854775808",
        "1e-9223372036854775809",
        "1e99999999999999999999999999999",
        // exponent fits but shifting in the fractional digits underflows it
        "0.1e-9223372036854775808",
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(overflow_cases); ++i) {
        ASSERT_NEW_FAILS(
            AWS_ERROR_OVERFLOW_DETECTED,
            aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(overflow_cases[i])),
            "input: %s",
            overflow_cases[i]);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_decimal_parse_invalid, s_big_decimal_parse_invalid_fn)

static int s_big_decimal_to_str_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct big_str_case cases[] = {
        {"-123.45", "-12345e-2"},
        {"-0.000123", "-123e-6"},
        {"-1.23E+10", "-123e8"},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        size_t expected_len = strlen(cases[i].expected);

        struct aws_big_decimal *v =
            aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i].input));
        ASSERT_NOT_NULL(v);

        uint8_t storage[32];
        struct aws_byte_buf fixed = aws_byte_buf_from_empty_array(storage, expected_len - 1);
        ASSERT_ERROR(
            AWS_ERROR_DEST_COPY_TOO_SMALL, aws_byte_buf_append_big_decimal(&fixed, v), "input: %s", cases[i].input);
        ASSERT_UINT_EQUALS(0, fixed.len);

        fixed = aws_byte_buf_from_empty_array(storage, expected_len);
        ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&fixed, v));
        ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&fixed), cases[i].expected);

        aws_big_decimal_destroy(v);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_decimal_to_str_buffer, s_big_decimal_to_str_buffer_fn)

static int s_big_parse_raw_cursor_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    static const uint8_t embedded_nul[] = {'1', '\0', '2'};
    static const uint8_t high_byte_int[] = {'1', 0xB2};
    static const uint8_t high_byte_frac[] = {'1', '.', 0xB2};
    static const uint8_t high_byte_exp[] = {'1', 'e', 0xB2};

    struct aws_byte_cursor int_cases[] = {
        {.len = 0, .ptr = NULL},
        aws_byte_cursor_from_array(embedded_nul, sizeof(embedded_nul)),
        aws_byte_cursor_from_array(high_byte_int, sizeof(high_byte_int)),
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(int_cases); ++i) {
        ASSERT_NEW_FAILS(
            AWS_ERROR_INVALID_ARGUMENT, aws_big_integer_new_from_cursor(allocator, int_cases[i]), "case %zu", i);
    }

    struct aws_byte_cursor dec_cases[] = {
        {.len = 0, .ptr = NULL},
        aws_byte_cursor_from_array(embedded_nul, sizeof(embedded_nul)),
        aws_byte_cursor_from_array(high_byte_int, sizeof(high_byte_int)),
        aws_byte_cursor_from_array(high_byte_frac, sizeof(high_byte_frac)),
        aws_byte_cursor_from_array(high_byte_exp, sizeof(high_byte_exp)),
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(dec_cases); ++i) {
        ASSERT_NEW_FAILS(
            AWS_ERROR_INVALID_ARGUMENT, aws_big_decimal_new_from_cursor(allocator, dec_cases[i]), "case %zu", i);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_parse_raw_cursor, s_big_parse_raw_cursor_fn)

static int s_big_decimal_to_str_append_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_big_decimal *v = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-123.45"));
    ASSERT_NOT_NULL(v);

    struct aws_byte_buf dynamic;
    ASSERT_SUCCESS(aws_byte_buf_init_copy_from_cursor(&dynamic, allocator, aws_byte_cursor_from_c_str("x=")));
    ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&dynamic, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&dynamic), "x=-12345e-2");

    uint8_t storage[16] = {'x', '='};
    struct aws_byte_buf fixed = aws_byte_buf_from_empty_array(storage, sizeof(storage));
    fixed.len = 2;
    ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&fixed, v));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&fixed), "x=-12345e-2");

    aws_byte_buf_clean_up(&dynamic);
    aws_big_decimal_destroy(v);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_decimal_to_str_append, s_big_decimal_to_str_append_fn)

static int s_big_destroy_null_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    aws_big_integer_destroy(NULL);
    aws_big_decimal_destroy(NULL);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_destroy_null, s_big_destroy_null_fn)

// The magnitude limit and the digit limit describe the same set of values: |v| < 2^16384.
static int s_big_limits_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    // 256 64-bit words, and the number of decimal digits in 2^16384 - 1
    enum { MAX_BYTES = 2048, MAX_DIGITS = 4933 };

    // 2^16384 - 1, the largest magnitude, is accepted and prints to exactly MAX_DIGITS digits
    uint8_t *bytes = aws_mem_acquire(allocator, MAX_BYTES + 100);
    ASSERT_NOT_NULL(bytes);
    memset(bytes, 0xff, MAX_BYTES);

    struct aws_big_integer *largest =
        aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, MAX_BYTES), false);
    ASSERT_NOT_NULL(largest);
    struct aws_byte_buf largest_str;
    ASSERT_SUCCESS(aws_byte_buf_init(&largest_str, allocator, 1));
    ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&largest_str, largest));
    ASSERT_UINT_EQUALS(MAX_DIGITS, largest_str.len);
    ASSERT_UINT_EQUALS('5', largest_str.buffer[largest_str.len - 1]); // 2^16384 ends in 6

    // what the library prints can always be parsed back
    struct aws_big_integer *reparsed =
        aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&largest_str));
    ASSERT_NOT_NULL(reparsed);
    ASSERT_SUCCESS(s_check_magnitude_equals(largest, reparsed, allocator));
    aws_big_integer_destroy(reparsed);

    // leading zero bytes do not count
    memmove(bytes + 100, bytes, MAX_BYTES);
    memset(bytes, 0, 100);
    struct aws_big_integer *padded =
        aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, MAX_BYTES + 100), false);
    ASSERT_NOT_NULL(padded);
    ASSERT_SUCCESS(s_check_magnitude_equals(largest, padded, allocator));
    aws_big_integer_destroy(padded);

    // leading zero digits do not count
    struct aws_byte_buf zero_padded;
    ASSERT_SUCCESS(aws_byte_buf_init(&zero_padded, allocator, largest_str.len + 1000));
    for (size_t i = 0; i < 1000; ++i) {
        aws_byte_buf_write_u8(&zero_padded, '0');
    }
    aws_byte_buf_write_from_whole_buffer(&zero_padded, largest_str);
    padded = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&zero_padded));
    ASSERT_NOT_NULL(padded);
    ASSERT_SUCCESS(s_check_magnitude_equals(largest, padded, allocator));
    aws_big_integer_destroy(padded);
    aws_byte_buf_clean_up(&zero_padded);

    // 2^16384 is rejected by the magnitude parser ...
    memset(bytes, 0, MAX_BYTES + 1);
    bytes[0] = 1;
    ASSERT_NEW_FAILS(
        AWS_ERROR_INVALID_ARGUMENT,
        aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, MAX_BYTES + 1), false));

    // ... and by the digit parser, even though it has only MAX_DIGITS digits
    struct aws_byte_buf too_big;
    ASSERT_SUCCESS(aws_byte_buf_init_copy(&too_big, allocator, &largest_str));
    too_big.buffer[too_big.len - 1] = '6';
    ASSERT_NEW_FAILS(
        AWS_ERROR_INVALID_ARGUMENT, aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&too_big)));

    // MAX_DIGITS nines is within the digit limit but above 2^16384
    memset(too_big.buffer, '9', too_big.len);
    ASSERT_NEW_FAILS(
        AWS_ERROR_INVALID_ARGUMENT, aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&too_big)));
    aws_byte_buf_clean_up(&too_big);

    // more than MAX_DIGITS significant digits is rejected
    ASSERT_SUCCESS(aws_byte_buf_init(&too_big, allocator, MAX_DIGITS + 1));
    aws_byte_buf_write_u8(&too_big, '1');
    for (size_t i = 0; i < MAX_DIGITS; ++i) {
        aws_byte_buf_write_u8(&too_big, '0');
    }
    ASSERT_NEW_FAILS(
        AWS_ERROR_INVALID_ARGUMENT, aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&too_big)));
    aws_byte_buf_clean_up(&too_big);

    // decimals apply the limit to the mantissa, fractional digits included, and the exponent does not count
    enum { WHOLE_DIGITS = 2500 };
    struct aws_byte_buf decimal_str;
    ASSERT_SUCCESS(aws_byte_buf_init(&decimal_str, allocator, MAX_DIGITS + 32));
    aws_byte_buf_write(&decimal_str, largest_str.buffer, WHOLE_DIGITS);
    aws_byte_buf_write_u8(&decimal_str, '.');
    aws_byte_buf_write(&decimal_str, largest_str.buffer + WHOLE_DIGITS, MAX_DIGITS - WHOLE_DIGITS);
    aws_byte_buf_write_from_whole_cursor(&decimal_str, aws_byte_cursor_from_c_str("e-99999"));

    struct aws_big_decimal *decimal =
        aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_buf(&decimal_str));
    ASSERT_NOT_NULL(decimal);
    ASSERT_SUCCESS(s_check_magnitude_equals(largest, aws_big_decimal_get_mantissa(decimal), allocator));
    ASSERT_INT_EQUALS(-99999 - (MAX_DIGITS - WHOLE_DIGITS), aws_big_decimal_get_exponent(decimal));
    aws_big_decimal_destroy(decimal);

    decimal_str.buffer[WHOLE_DIGITS + 1 + (MAX_DIGITS - WHOLE_DIGITS) - 1] = '6'; // 2^16384
    ASSERT_NEW_FAILS(
        AWS_ERROR_INVALID_ARGUMENT, aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_buf(&decimal_str)));
    aws_byte_buf_clean_up(&decimal_str);

    aws_big_integer_destroy(largest);
    aws_byte_buf_clean_up(&largest_str);
    aws_mem_release(allocator, bytes);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_limits, s_big_limits_fn)

static struct aws_big_integer *s_parse(struct aws_allocator *allocator, const char *str) {
    return aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(str));
}

// Returns -v, built from the public API.
static struct aws_big_integer *s_negate(struct aws_allocator *allocator, const struct aws_big_integer *v) {
    struct aws_byte_buf magnitude;
    if (aws_byte_buf_init(&magnitude, allocator, 1)) {
        return NULL;
    }
    struct aws_big_integer *result = NULL;
    if (aws_big_integer_get_magnitude_be(v, &magnitude) == AWS_OP_SUCCESS) {
        result = aws_big_integer_new(allocator, aws_byte_cursor_from_buf(&magnitude), aws_big_integer_get_sign(v) > 0);
    }
    aws_byte_buf_clean_up(&magnitude);
    return result;
}

enum { LARGE_DIGIT_COUNT = 2400 };

static int s_big_large_input_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    // "-" + LARGE_DIGIT_COUNT digits + "." + LARGE_DIGIT_COUNT digits + NUL
    struct aws_byte_buf input;
    ASSERT_SUCCESS(aws_byte_buf_init(&input, allocator, 2 * LARGE_DIGIT_COUNT + 3));
    struct aws_byte_buf expected;
    ASSERT_SUCCESS(aws_byte_buf_init(&expected, allocator, 2 * LARGE_DIGIT_COUNT + 16));

    aws_byte_buf_write_u8(&input, '-');
    for (size_t i = 0; i < LARGE_DIGIT_COUNT; ++i) {
        aws_byte_buf_write_u8(&input, (uint8_t)('1' + i % 9));
    }
    aws_byte_buf_write_u8(&input, '\0');

    ASSERT_SUCCESS(s_check_big_integer_round_trip(allocator, (const char *)input.buffer, (const char *)input.buffer));
    --input.len;

    aws_byte_buf_write_u8(&expected, '-');
    aws_byte_buf_write_from_whole_buffer(&expected, aws_byte_buf_from_array(input.buffer + 1, LARGE_DIGIT_COUNT));
    aws_byte_buf_write_u8(&input, '.');
    for (size_t i = 0; i < LARGE_DIGIT_COUNT; ++i) {
        uint8_t digit = (uint8_t)('0' + i % 10);
        aws_byte_buf_write_u8(&input, digit);
        aws_byte_buf_write_u8(&expected, digit);
    }
    aws_byte_buf_write_u8(&input, '\0');
    aws_byte_buf_write_from_whole_cursor(&expected, aws_byte_cursor_from_c_str("e-2400"));
    aws_byte_buf_write_u8(&expected, '\0');

    ASSERT_SUCCESS(
        s_check_big_decimal_round_trip(allocator, (const char *)input.buffer, (const char *)expected.buffer));

    aws_byte_buf_clean_up(&expected);
    aws_byte_buf_clean_up(&input);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_large_input, s_big_large_input_fn)

static int s_big_decimal_new_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *mantissas[] = {"0", "1", "-1", "18446744073709551616", "-123456789012345678901234567890"};
    int64_t exponents[] = {0, 5, -5, INT64_MAX, INT64_MIN};

    for (size_t i = 0; i < AWS_ARRAY_SIZE(mantissas); ++i) {
        for (size_t j = 0; j < AWS_ARRAY_SIZE(exponents); ++j) {
            struct aws_big_integer *mantissa =
                aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(mantissas[i]));
            ASSERT_NOT_NULL(mantissa);
            struct aws_big_decimal *decimal = aws_big_decimal_new(allocator, mantissa, exponents[j]);
            ASSERT_NOT_NULL(decimal);

            // The mantissa was copied
            aws_big_integer_destroy(mantissa);
            ASSERT_INT_EQUALS(exponents[j], aws_big_decimal_get_exponent(decimal));

            // It round trips through a string
            struct aws_byte_buf str;
            ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 1));
            ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&str, decimal));
            struct aws_big_decimal *parsed = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_buf(&str));
            ASSERT_NOT_NULL(parsed);
            ASSERT_INT_EQUALS(exponents[j], aws_big_decimal_get_exponent(parsed));
            ASSERT_SUCCESS(s_check_magnitude_equals(
                aws_big_decimal_get_mantissa(decimal), aws_big_decimal_get_mantissa(parsed), allocator));

            aws_big_decimal_destroy(parsed);
            aws_byte_buf_clean_up(&str);
            aws_big_decimal_destroy(decimal);
        }
    }

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(big_decimal_new, s_big_decimal_new_fn)

static int s_big_integer_eq_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *values[] = {
        "0",
        "1",
        "-1",
        "18446744073709551615",
        "18446744073709551616",
        "-18446744073709551616",
        "-18446744073709551617",
        "36893488147419103232",
        "123456789012345678901234567890123456789012345678901234567890",
        "-123456789012345678901234567890123456789012345678901234567890",
    };

    // Each value equals itself, including a separately constructed copy with leading zeros and a redundant plus,
    // and nothing else.
    for (size_t i = 0; i < AWS_ARRAY_SIZE(values); ++i) {
        struct aws_big_integer *a = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(values[i]));
        ASSERT_NOT_NULL(a);
        ASSERT_TRUE(aws_big_integer_eq(a, a));

        struct aws_byte_buf padded;
        ASSERT_SUCCESS(aws_byte_buf_init(&padded, allocator, 1));
        bool negative = values[i][0] == '-';
        ASSERT_SUCCESS(aws_byte_buf_append_byte_dynamic(&padded, negative ? '-' : '+'));
        ASSERT_SUCCESS(aws_byte_buf_append_byte_dynamic(&padded, '0'));
        ASSERT_SUCCESS(aws_byte_buf_append_byte_dynamic(&padded, '0'));
        struct aws_byte_cursor digits = aws_byte_cursor_from_c_str(values[i] + (negative ? 1 : 0));
        ASSERT_SUCCESS(aws_byte_buf_append_dynamic(&padded, &digits));
        struct aws_big_integer *b = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&padded));
        ASSERT_NOT_NULL(b);
        ASSERT_TRUE(aws_big_integer_eq(a, b));
        ASSERT_TRUE(aws_big_integer_eq(b, a));
        aws_big_integer_destroy(b);
        aws_byte_buf_clean_up(&padded);

        for (size_t j = 0; j < AWS_ARRAY_SIZE(values); ++j) {
            if (i == j) {
                continue;
            }
            struct aws_big_integer *other =
                aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(values[j]));
            ASSERT_NOT_NULL(other);
            ASSERT_FALSE(aws_big_integer_eq(a, other));
            aws_big_integer_destroy(other);
        }

        aws_big_integer_destroy(a);
    }

    // Zero has one representation however it is made.
    struct aws_big_integer *zero = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("0"));
    struct aws_big_integer *negative_zero =
        aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-0"));
    struct aws_big_integer *negated_zero = s_negate(allocator, zero);
    struct aws_big_integer *empty = aws_big_integer_new(allocator, aws_byte_cursor_from_array(NULL, 0), false);
    ASSERT_TRUE(aws_big_integer_eq(zero, negative_zero));
    ASSERT_TRUE(aws_big_integer_eq(zero, negated_zero));
    ASSERT_TRUE(aws_big_integer_eq(zero, empty));
    aws_big_integer_destroy(zero);
    aws_big_integer_destroy(negative_zero);
    aws_big_integer_destroy(negated_zero);
    aws_big_integer_destroy(empty);

    // Values built different ways compare equal.
    struct aws_big_integer *parsed = s_parse(allocator, "18446744073709551616");
    static const uint8_t bytes[] = {0x01, 0, 0, 0, 0, 0, 0, 0, 0};
    struct aws_big_integer *from_bytes =
        aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, sizeof(bytes)), false);
    ASSERT_TRUE(aws_big_integer_eq(parsed, from_bytes));
    aws_big_integer_destroy(parsed);
    aws_big_integer_destroy(from_bytes);

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(big_integer_eq, s_big_integer_eq_fn)

struct decimal_eq_case {
    const char *a;
    const char *b;
    bool expected;
};

static int s_big_decimal_eq_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    static const struct decimal_eq_case cases[] = {
        /* Same mantissa and exponent, however they are written. */
        {"1.50", "150e-2", true},
        {"1.50", "+0001.50", true},
        {"150e-2", "150E-2", true},
        {"0", "0e0", true},
        {"0e5", "-0e5", true},
        {"-1.5", "-15e-1", true},
        {"123456789012345678901234567890e-10", "12345678901234567890.1234567890", true},
        {"18446744073709551616e1", "18446744073709551616e1", true},
        {"1e9223372036854775807", "1e9223372036854775807", true},
        {"1e-9223372036854775808", "1e-9223372036854775808", true},
        /* The same numeric value with a different scale is not equal. */
        {"1.5", "1.50", false},
        {"15e1", "150", false},
        {"15e1", "150e0", false},
        {"1000", "1e3", false},
        {"0e0", "0e1", false},
        {"0.0", "0.00", false},
        /* Different mantissa or exponent. */
        {"1e0", "-1e0", false},
        {"1e0", "2e0", false},
        {"15e1", "15e2", false},
        {"18446744073709551616e0", "18446744073709551617e0", false},
        {"1e9223372036854775807", "1e-9223372036854775808", false},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        struct aws_big_decimal *a = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i].a));
        struct aws_big_decimal *b = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i].b));
        ASSERT_NOT_NULL(a, "case %zu", i);
        ASSERT_NOT_NULL(b, "case %zu", i);
        ASSERT_TRUE(aws_big_decimal_eq(a, a), "case %zu", i);
        ASSERT_TRUE(aws_big_decimal_eq(b, b), "case %zu", i);
        ASSERT_INT_EQUALS(cases[i].expected, aws_big_decimal_eq(a, b), "case %zu: %s vs %s", i, cases[i].a, cases[i].b);
        ASSERT_INT_EQUALS(cases[i].expected, aws_big_decimal_eq(b, a), "case %zu: %s vs %s", i, cases[i].b, cases[i].a);
        aws_big_decimal_destroy(a);
        aws_big_decimal_destroy(b);
    }

    /* A decimal built from parts equals the parsed one. */
    struct aws_big_integer *mantissa = s_parse(allocator, "-18446744073709551617");
    struct aws_big_decimal *from_parts = aws_big_decimal_new(allocator, mantissa, -3);
    struct aws_big_decimal *parsed =
        aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-18446744073709551617e-3"));
    ASSERT_NOT_NULL(from_parts);
    ASSERT_NOT_NULL(parsed);
    ASSERT_TRUE(aws_big_decimal_eq(from_parts, parsed));
    aws_big_decimal_destroy(from_parts);
    aws_big_decimal_destroy(parsed);
    aws_big_integer_destroy(mantissa);

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(big_decimal_eq, s_big_decimal_eq_fn)

static int s_big_integer_get_sign_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct {
        const char *input;
        int sign;
    } cases[] = {
        {"0", 0},
        {"-0", 0},
        {"+0", 0},
        {"1", 1},
        {"-1", -1},
        {"18446744073709551616", 1},
        {"-18446744073709551616", -1},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        struct aws_big_integer *v =
            aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(cases[i].input));
        ASSERT_NOT_NULL(v);
        ASSERT_INT_EQUALS(cases[i].sign, aws_big_integer_get_sign(v), "input %s", cases[i].input);

        // Negating flips every sign except zero's.
        struct aws_big_integer *negated = s_negate(allocator, v);
        ASSERT_NOT_NULL(negated);
        ASSERT_INT_EQUALS(-cases[i].sign, aws_big_integer_get_sign(negated), "negated input %s", cases[i].input);

        aws_big_integer_destroy(negated);
        aws_big_integer_destroy(v);
    }

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(big_integer_get_sign, s_big_integer_get_sign_fn)

// The bound is never short, and at most one byte over, for every sign and exponent width.
static int s_big_decimal_max_strlen_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *mantissas[] = {
        "0",
        "1",
        "-1",
        "9",
        "10",
        "-99",
        "18446744073709551615",
        "18446744073709551616",
        "-18446744073709551616",
        "1000000000000000000000000000000000000000",
    };
    const int64_t exponents[] = {
        0,
        1,
        -1,
        9,
        10,
        -10,
        99,
        100,
        -100,
        999999999,
        INT64_MAX,
        INT64_MIN,
        INT64_MIN + 1,
    };

    for (size_t m = 0; m < AWS_ARRAY_SIZE(mantissas); ++m) {
        struct aws_big_integer *mantissa =
            aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(mantissas[m]));
        ASSERT_NOT_NULL(mantissa);

        for (size_t e = 0; e < AWS_ARRAY_SIZE(exponents); ++e) {
            struct aws_big_decimal *v = aws_big_decimal_new(allocator, mantissa, exponents[e]);
            ASSERT_NOT_NULL(v);

            struct aws_byte_buf grown;
            ASSERT_SUCCESS(aws_byte_buf_init(&grown, allocator, 0));
            ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&grown, v));

            size_t max_strlen = aws_big_decimal_max_strlen(v);
            ASSERT_TRUE(max_strlen >= grown.len, "mantissa %s exponent %lld", mantissas[m], (long long)exponents[e]);
            ASSERT_TRUE(
                max_strlen <= grown.len + 1, "mantissa %s exponent %lld", mantissas[m], (long long)exponents[e]);

            // a fixed buffer of exactly the bound is big enough
            struct aws_byte_buf fixed;
            ASSERT_SUCCESS(aws_byte_buf_init(&fixed, allocator, max_strlen));
            fixed.allocator = NULL;
            ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&fixed, v));
            ASSERT_TRUE(aws_byte_buf_eq(&grown, &fixed));
            aws_mem_release(allocator, fixed.buffer);

            aws_byte_buf_clean_up(&grown);
            aws_big_decimal_destroy(v);
        }
        aws_big_integer_destroy(mantissa);
    }

    // the largest mantissa
    uint8_t *bytes = aws_mem_acquire(allocator, 2048);
    ASSERT_NOT_NULL(bytes);
    memset(bytes, 0xff, 2048);
    struct aws_big_integer *largest = aws_big_integer_new(allocator, aws_byte_cursor_from_array(bytes, 2048), true);
    ASSERT_NOT_NULL(largest);
    struct aws_big_decimal *v = aws_big_decimal_new(allocator, largest, INT64_MIN);
    ASSERT_NOT_NULL(v);
    struct aws_byte_buf grown;
    ASSERT_SUCCESS(aws_byte_buf_init(&grown, allocator, 0));
    ASSERT_SUCCESS(aws_byte_buf_append_big_decimal(&grown, v));
    ASSERT_TRUE(aws_big_decimal_max_strlen(v) >= grown.len);
    ASSERT_TRUE(aws_big_decimal_max_strlen(v) <= grown.len + 1);
    aws_byte_buf_clean_up(&grown);
    aws_big_decimal_destroy(v);
    aws_big_integer_destroy(largest);
    aws_mem_release(allocator, bytes);

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(big_decimal_max_strlen, s_big_decimal_max_strlen_fn)

// splitmix64, so that the inputs below can be reproduced by an independent implementation.
static uint64_t s_splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t s_fnv1a64(struct aws_byte_cursor str) {
    uint64_t hash = 0xcbf29ce484222325ULL;
    for (size_t i = 0; i < str.len; ++i) {
        hash ^= str.ptr[i];
        hash *= 0x100000001b3ULL;
    }
    return hash;
}

struct big_reference_case {
    size_t magnitude_len;
    uint64_t seed;
    bool is_negative;
    size_t expected_str_len;
    uint64_t expected_str_hash;
};

/*
 * Large values can't be checked against a literal without a multi-KB source file, so the base-10 expectation is a
 * length and an FNV-1a hash of the string. Both were computed with Python's int, from the same big-endian bytes (the
 * splitmix64 outputs, 8 bytes each, truncated to magnitude_len).
 */
static int s_big_integer_reference_vectors_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    static const struct big_reference_case cases[] = {
        {1, 0x1000ULL, false, 3, 0x603b3f18278a717bULL},
        {7, 0x1001ULL, true, 18, 0x2cbff55ddf30d38fULL},
        {8, 0x1002ULL, false, 20, 0x1e96ff16f2a8cba3ULL},
        {9, 0x1003ULL, true, 23, 0x711213aaf01adedbULL},
        {15, 0x1004ULL, false, 36, 0x44e42481bee2f512ULL},
        {16, 0x1005ULL, true, 40, 0x264693142a54ebd0ULL},
        {17, 0x1006ULL, false, 41, 0x43b2d9ae6fda49b1ULL},
        {63, 0x1007ULL, true, 153, 0xaa3d0dd38548fd04ULL},
        {64, 0x1008ULL, false, 154, 0x842f98c1f05d5ef0ULL},
        {65, 0x1009ULL, true, 157, 0xa43c51bd3a420057ULL},
        {200, 0x100aULL, false, 482, 0x698ca8b0ccfbbfdcULL},
        {512, 0x100bULL, true, 1235, 0x1cf779e7a851cf2bULL},
        {1000, 0x100cULL, false, 2409, 0x57b51ba6f7abf6bdULL},
        {2047, 0x100fULL, true, 4931, 0x7fa396e21e9dd4fcULL},
        {2048, 0x1010ULL, false, 4932, 0x1e52dfd3b048c0ecULL},
    };

    for (size_t i = 0; i < AWS_ARRAY_SIZE(cases); ++i) {
        const struct big_reference_case *c = &cases[i];

        uint8_t magnitude[2048 + 8];
        uint64_t state = c->seed;
        for (size_t offset = 0; offset < c->magnitude_len; offset += 8) {
            uint64_t word = s_splitmix64(&state);
            for (size_t b = 0; b < 8; ++b) {
                magnitude[offset + b] = (uint8_t)(word >> (8 * (7 - b)));
            }
        }

        struct aws_big_integer *v =
            aws_big_integer_new(allocator, aws_byte_cursor_from_array(magnitude, c->magnitude_len), c->is_negative);
        ASSERT_NOT_NULL(v, "case %zu", i);

        struct aws_byte_buf str;
        ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 1));
        ASSERT_SUCCESS(aws_byte_buf_append_big_integer(&str, v));
        ASSERT_UINT_EQUALS(c->expected_str_len, str.len, "case %zu", i);
        ASSERT_TRUE(c->expected_str_hash == s_fnv1a64(aws_byte_cursor_from_buf(&str)), "case %zu", i);

        // The string is now known good, so parsing it back checks the other direction.
        struct aws_big_integer *parsed = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_buf(&str));
        ASSERT_NOT_NULL(parsed, "case %zu", i);
        ASSERT_TRUE(aws_big_integer_eq(v, parsed), "case %zu", i);

        aws_big_integer_destroy(parsed);
        aws_byte_buf_clean_up(&str);
        aws_big_integer_destroy(v);
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(big_integer_reference_vectors, s_big_integer_reference_vectors_fn)
