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

#define BASE_BITS 32
#define NIBBLES_PER_DIGIT ((BASE_BITS) / 4)
#define LOWER_32_BIT_MASK 0xFFFFFFFF
#define INT64_MIN_AS_HEX 0x8000000000000000

/*
 * Working set of invariants:
 *
 * (1) Negative zero is illegal
 * (2) The only time leading (trailing) 0-value digits are allowed is a single instance to represent actual zero.
 *
 * Other proposals:
 *
 * (1) Functionally immutable API (no visible side-affects)
 * (2) params may be temporarily altered during computation before being restored ub irder to prevent pointless copying
 *   (most often around sign negation and operator switching)
 *
 * Dev ideas:
 *
 * (1) Internal arithmetic ops may use a "raw" interface to allow for subsequence operations used in multiply/divide.
 */

void aws_bigint_clean_up(struct aws_bigint *bigint) {
    aws_array_list_clean_up(&bigint->digits);
}

int aws_bigint_init(struct aws_bigint *bigint, struct aws_allocator *allocator) {
    return aws_bigint_init_reserve(bigint, allocator, 0);
}

int aws_bigint_init_reserve(struct aws_bigint *bigint, struct aws_allocator *allocator, uint64_t reserve_bits) {
    uint64_t digit_count = reserve_bits == 0 ? 1 : (reserve_bits - 1) / BASE_BITS + 1;

    if (aws_array_list_init_dynamic(&bigint->digits, allocator, digit_count, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    uint32_t zero = 0;
    aws_array_list_push_back(&bigint->digits, &zero);

    bigint->sign = 1;

    return AWS_OP_SUCCESS;
}

static void s_advance_cursor_to_hex_start(struct aws_byte_cursor *hex_cursor) {
    if (hex_cursor->len >= 2) {
        const char *raw_ptr = (char *)hex_cursor->ptr;
        if (raw_ptr[0] == '0' && (raw_ptr[1] == 'x' || raw_ptr[1] == 'X')) {
            aws_byte_cursor_advance(hex_cursor, 2);
        }

        while (hex_cursor->len > 0 && *hex_cursor->ptr == '0') {
            aws_byte_cursor_advance(hex_cursor, 1);
        }
    } else if (hex_cursor->len == 1) {
        if (*hex_cursor->ptr == '0') {
            aws_byte_cursor_advance(hex_cursor, 1);
        }
    }
}

static int s_uint32_from_hex(struct aws_byte_cursor digit_cursor, uint32_t *output_value) {
    AWS_FATAL_ASSERT(digit_cursor.len <= NIBBLES_PER_DIGIT);

    *output_value = 0;

    while (digit_cursor.len > 0) {
        char hex_digit = *digit_cursor.ptr;
        uint32_t hex_value = 0;
        if (hex_digit <= '9' && hex_digit >= '0') {
            hex_value = hex_digit - '0';
        } else if (hex_digit <= 'f' && hex_digit >= 'a') {
            hex_value = hex_digit - 'a';
        } else if (hex_digit <= 'F' && hex_digit >= 'A') {
            hex_value = hex_digit - 'A';
        } else {
            return AWS_OP_ERR;
        }

        *output_value <<= 4;
        *output_value += hex_value;

        aws_byte_cursor_advance(&digit_cursor, 1);
    }

    return AWS_OP_SUCCESS;
}

int aws_bigint_init_from_hex(
    struct aws_bigint *bigint,
    struct aws_allocator *allocator,
    struct aws_byte_cursor hex_digits) {
    s_advance_cursor_to_hex_start(&hex_digits);

    if (hex_digits.len == 0) {
        return aws_bigint_init(bigint, allocator);
    }

    uint64_t digit_count = hex_digits.len / BASE_BITS;
    if (aws_array_list_init_dynamic(&bigint->digits, allocator, digit_count, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    while (hex_digits.len > 0) {
        struct aws_byte_cursor digit_cursor = hex_digits;
        if (digit_cursor.len > NIBBLES_PER_DIGIT) {
            digit_cursor.ptr += (digit_cursor.len - NIBBLES_PER_DIGIT);
            digit_cursor.len = NIBBLES_PER_DIGIT;
        }

        uint32_t digit_value = 0;
        if (s_uint32_from_hex(digit_cursor, &digit_value)) {
            goto on_error;
        }

        aws_array_list_push_back(&bigint->digits, &digit_value);

        hex_digits.len -= digit_cursor.len;
    }

    bigint->sign = 1;

    return AWS_OP_SUCCESS;

on_error:

    aws_bigint_clean_up(bigint);

    return AWS_OP_ERR;
}

int aws_bigint_init_from_int64(struct aws_bigint *bigint, struct aws_allocator *allocator, int64_t value) {
    if (value > 0) {
        return aws_bigint_init_from_uint64(bigint, allocator, (uint64_t)value);
    }

    if (value == INT64_MIN) {
        if (aws_bigint_init_from_uint64(bigint, allocator, INT64_MIN_AS_HEX)) {
            return AWS_OP_ERR;
        }
    } else {
        if (aws_bigint_init_from_uint64(bigint, allocator, (uint64_t)(-value))) {
            return AWS_OP_ERR;
        }
    }

    bigint->sign = -1;

    return AWS_OP_SUCCESS;
}

int aws_bigint_init_from_uint64(struct aws_bigint *bigint, struct aws_allocator *allocator, uint64_t value) {

    uint32_t lower_digit = (uint32_t)(value & LOWER_32_BIT_MASK);
    uint32_t upper_digit = (uint32_t)((value >> 32) & LOWER_32_BIT_MASK);
    uint64_t digit_count = upper_digit > 0 ? 2 : 1;
    if (aws_array_list_init_dynamic(&bigint->digits, allocator, digit_count, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    aws_array_list_push_back(&bigint->digits, &lower_digit);

    if (upper_digit > 0) {
        aws_array_list_push_back(&bigint->digits, &upper_digit);
    }

    bigint->sign = 1;

    return AWS_OP_SUCCESS;
}

static const uint8_t *HEX_CHARS = (const uint8_t *)"0123456789abcdef";

static void s_append_uint32_as_hex(struct aws_byte_buf *buffer, uint32_t value, bool prepend_zeros) {

    bool have_seen_non_zero_nibble = false;
    size_t write_index = buffer->len;
    for (size_t i = 0; i < NIBBLES_PER_DIGIT; ++i) {
        uint8_t high_nibble = (uint8_t)(value >> 28);
        AWS_FATAL_ASSERT(high_nibble < 16);

        if (high_nibble > 0) {
            have_seen_non_zero_nibble = true;
        }

        if (have_seen_non_zero_nibble || prepend_zeros || i + 1 == NIBBLES_PER_DIGIT) {
            AWS_FATAL_ASSERT(write_index < buffer->capacity);
            buffer->buffer[write_index++] = HEX_CHARS[high_nibble];
        }

        value <<= 4;
    }

    buffer->len = write_index;
}

int aws_bigint_bytebuf_append_as_hex(struct aws_bigint *bigint, struct aws_byte_buf *buffer) {
    size_t digit_count = aws_array_list_length(&bigint->digits);
    uint64_t max_hex_digits = aws_array_list_length(&bigint->digits) * NIBBLES_PER_DIGIT;
    uint64_t total_characters = max_hex_digits + ((bigint->sign < 0) ? 1 : 0);
    if (aws_byte_buf_reserve_relative(buffer, total_characters)) {
        return AWS_OP_ERR;
    }

    /*
     * We don't support negative hex numbers from an initialization standpoint, but we still
     * need to indicate the number's sign on output
     */
    if (bigint->sign < 0) {
        buffer->buffer[buffer->len++] = '-';
    }

    for (size_t i = 0; i < digit_count; i++) {
        size_t digit_index = digit_count - i - 1;
        uint32_t digit = 0;
        if (aws_array_list_get_at(&bigint->digits, &digit, digit_index)) {
            return AWS_OP_ERR;
        }

        bool prepend_zeros = i != 0;
        s_append_uint32_as_hex(buffer, digit, prepend_zeros);
    }

    return AWS_OP_SUCCESS;
}

bool aws_bigint_is_negative(struct aws_bigint *bigint) {
    return bigint->sign < 0;
}

bool aws_bigint_is_positive(struct aws_bigint *bigint) {
    return bigint->sign > 0;
}

bool aws_bigint_is_zero(struct aws_bigint *bigint) {
    if (bigint->sign < 0) {
        return false;
    }

    size_t digit_count = aws_array_list_length(&bigint->digits);
    if (digit_count != 1) {
        return false;
    }

    uint32_t digit = 0;
    aws_array_list_get_at(&bigint->digits, &digit, 0);

    return digit == 0;
}

bool aws_bigint_equals(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    size_t lhs_digit_count = aws_array_list_length(&lhs->digits);
    size_t rhs_digit_count = aws_array_list_length(&rhs->digits);

    if (lhs_digit_count != rhs_digit_count) {
        return false;
    }

    for (size_t i = 0; i < lhs_digit_count; ++i) {
        uint32_t lhs_digit = 0;
        uint32_t rhs_digit = 0;

        aws_array_list_get_at(&lhs->digits, &lhs_digit, i);
        aws_array_list_get_at(&rhs->digits, &rhs_digit, i);

        if (lhs_digit != rhs_digit) {
            return false;
        }
    }

    return true;
}

bool aws_bigint_not_equals(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    return !aws_bigint_equals(lhs, rhs);
}

bool aws_bigint_less_than(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    size_t lhs_digit_count = aws_array_list_length(&lhs->digits);
    size_t rhs_digit_count = aws_array_list_length(&rhs->digits);

    if (lhs_digit_count < rhs_digit_count) {
        return true;
    } else if (lhs_digit_count > rhs_digit_count) {
        return false;
    }

    for (size_t i = 0; i < lhs_digit_count; ++i) {
        size_t digit_index = lhs_digit_count - i - 1;
        uint32_t lhs_digit = 0;
        uint32_t rhs_digit = 0;

        aws_array_list_get_at(&lhs->digits, &lhs_digit, digit_index);
        aws_array_list_get_at(&rhs->digits, &rhs_digit, digit_index);

        if (lhs_digit < rhs_digit) {
            return true;
        } else if (lhs_digit > rhs_digit) {
            return false;
        }
    }

    /* they're equal */
    return false;
}

bool aws_bigint_greater_than(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    size_t lhs_digit_count = aws_array_list_length(&lhs->digits);
    size_t rhs_digit_count = aws_array_list_length(&rhs->digits);

    if (lhs_digit_count < rhs_digit_count) {
        return false;
    } else if (lhs_digit_count > rhs_digit_count) {
        return true;
    }

    for (size_t i = 0; i < lhs_digit_count; ++i) {
        size_t digit_index = lhs_digit_count - i - 1;
        uint32_t lhs_digit = 0;
        uint32_t rhs_digit = 0;

        aws_array_list_get_at(&lhs->digits, &lhs_digit, digit_index);
        aws_array_list_get_at(&rhs->digits, &rhs_digit, digit_index);

        if (lhs_digit < rhs_digit) {
            return false;
        } else if (lhs_digit > rhs_digit) {
            return true;
        }
    }

    /* they're equal */
    return false;
}

bool aws_bigint_less_than_or_equals(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    return !aws_bigint_greater_than(lhs, rhs);
}

bool aws_bigint_greater_than_or_equals(struct aws_bigint *lhs, struct aws_bigint *rhs) {
    return !aws_bigint_less_than(lhs, rhs);
}

void aws_bigint_negate(struct aws_bigint *bigint) {
    if (!aws_bigint_is_zero(bigint)) {
        bigint->sign *= -1;
    }
}
