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
 * (2) params may be temporarily altered during computation before being restored in order to prevent pointless copying
 *   (most often around sign negation and operator switching)
 *
 * Dev ideas:
 *
 * (1) Internal arithmetic ops may use a "raw" interface to allow for subsequence operations used in multiply/divide.
 */

void aws_bigint_clean_up(struct aws_bigint *bigint) {
    aws_array_list_clean_up_secure(&bigint->digits);
}

static void s_advance_cursor_past_hex_prefix(struct aws_byte_cursor *hex_cursor) {
    if (hex_cursor->len >= 2) {
        const char *raw_ptr = (char *)hex_cursor->ptr;
        if (raw_ptr[0] == '0' && (raw_ptr[1] == 'x' || raw_ptr[1] == 'X')) {
            aws_byte_cursor_advance(hex_cursor, 2);
        }
    }
}

static void s_advance_cursor_to_non_zero(struct aws_byte_cursor *hex_cursor) {
    while (hex_cursor->len > 0 && *hex_cursor->ptr == '0') {
        aws_byte_cursor_advance(hex_cursor, 1);
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
            hex_value = hex_digit - 'a' + 10;
        } else if (hex_digit <= 'F' && hex_digit >= 'A') {
            hex_value = hex_digit - 'A' + 10;
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

    /* skip past the optional "0x" prefix */
    s_advance_cursor_past_hex_prefix(&hex_digits);
    if (hex_digits.len == 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    /* skip past leading zeros */
    s_advance_cursor_to_non_zero(&hex_digits);
    if (hex_digits.len == 0) {
        return aws_bigint_init_from_uint64(bigint, allocator, 0);
    }

    uint64_t digit_count = hex_digits.len / BASE_BITS + 1;
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
            aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
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
    if (value >= 0) {
        return aws_bigint_init_from_uint64(bigint, allocator, (uint64_t)value);
    }

    if (value == INT64_MIN) {
        /* We can't just negate and cast, so just submit a constant */
        if (aws_bigint_init_from_uint64(bigint, allocator, INT64_MIN_AS_HEX)) {
            return AWS_OP_ERR;
        }
    } else {
        /* The value is negative but can be safely negated to a positive value before casting to uint64 */
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

int aws_bigint_init_from_copy(struct aws_bigint *bigint, const struct aws_bigint *source) {
    bigint->sign = source->sign;

    size_t source_length = aws_array_list_length(&source->digits);
    if (aws_array_list_init_dynamic(&bigint->digits, source->digits.alloc, source_length, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    for (size_t i = 0; i < source_length; ++i) {
        uint32_t digit = 0;
        aws_array_list_get_at(&source->digits, &digit, i);

        aws_array_list_push_back(&bigint->digits, &digit);
    }

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

int aws_bigint_bytebuf_debug_output(const struct aws_bigint *bigint, struct aws_byte_buf *buffer) {
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

bool aws_bigint_is_negative(const struct aws_bigint *bigint) {
    return bigint->sign < 0;
}

bool aws_bigint_is_positive(const struct aws_bigint *bigint) {
    return bigint->sign > 0 && !aws_bigint_is_zero(bigint);
}

bool aws_bigint_is_zero(const struct aws_bigint *bigint) {
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

enum aws_bigint_ordering {
    AWS_BI_LESS_THAN,
    AWS_BI_EQUAL_TO,
    AWS_BI_GREATER_THAN,
};

static enum aws_bigint_ordering s_aws_bigint_get_magnitude_ordering(
    const struct aws_bigint *lhs,
    const struct aws_bigint *rhs) {
    size_t lhs_digit_count = aws_array_list_length(&lhs->digits);
    size_t rhs_digit_count = aws_array_list_length(&rhs->digits);

    if (lhs_digit_count < rhs_digit_count) {
        return AWS_BI_LESS_THAN;
    } else if (lhs_digit_count > rhs_digit_count) {
        return AWS_BI_GREATER_THAN;
    }

    for (size_t i = 0; i < lhs_digit_count; ++i) {
        uint32_t lhs_digit = 0;
        uint32_t rhs_digit = 0;

        aws_array_list_get_at(&lhs->digits, &lhs_digit, lhs_digit_count - i - 1);
        aws_array_list_get_at(&rhs->digits, &rhs_digit, rhs_digit_count - i - 1);

        if (lhs_digit < rhs_digit) {
            return AWS_BI_LESS_THAN;
        } else if (lhs_digit > rhs_digit) {
            return AWS_BI_GREATER_THAN;
        }
    }

    return AWS_BI_EQUAL_TO;
}

bool aws_bigint_equals(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    return s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_EQUAL_TO && lhs->sign == rhs->sign;
}

bool aws_bigint_not_equals(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    return !aws_bigint_equals(lhs, rhs);
}

bool aws_bigint_less_than(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    if (lhs->sign < 0) {
        if (rhs->sign < 0) {
            return s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_GREATER_THAN;
        } else {
            return true;
        }
    } else {
        if (rhs->sign < 0) {
            return false;
        } else {
            return s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_LESS_THAN;
        }
    }
}

bool aws_bigint_greater_than(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    if (lhs->sign < 0) {
        if (rhs->sign < 0) {
            return s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_LESS_THAN;
        } else {
            return false;
        }
    } else {
        if (rhs->sign < 0) {
            return true;
        } else {
            return s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_GREATER_THAN;
        }
    }
}

bool aws_bigint_less_than_or_equals(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    return !aws_bigint_greater_than(lhs, rhs);
}

bool aws_bigint_greater_than_or_equals(const struct aws_bigint *lhs, const struct aws_bigint *rhs) {
    return !aws_bigint_less_than(lhs, rhs);
}

void aws_bigint_negate(struct aws_bigint *bigint) {
    if (!aws_bigint_is_zero(bigint)) {
        bigint->sign *= -1;
    }
}

static void s_aws_bigint_trim_leading_zeros(struct aws_bigint *bigint) {
    size_t length = aws_array_list_length(&bigint->digits);
    if (length == 0) {
        return;
    }

    size_t index = length - 1;
    while (index > 0) {
        uint32_t digit = 0;
        aws_array_list_get_at(&bigint->digits, &digit, index);
        if (digit == 0) {
            aws_array_list_pop_back(&bigint->digits);
        } else {
            return;
        }

        --index;
    }
}

static int s_aws_bigint_add_magnitudes(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs) {
    size_t lhs_length = aws_array_list_length(&lhs->digits);
    size_t rhs_length = aws_array_list_length(&rhs->digits);

    size_t reserved_digits = lhs_length;
    if (rhs_length > reserved_digits) {
        reserved_digits = rhs_length;
    }

    /*
     * We actually want to reserve (reserved_digits + 1) but the ensure_capacity api takes an index that needs to
     * be valid, so there's no need to do a final increment
     */
    if (aws_array_list_ensure_capacity(&output->digits, reserved_digits)) {
        return AWS_OP_ERR;
    }

    size_t output_length = aws_array_list_length(&output->digits);

    /*
     * Nothing should fail after this point
     */
    uint64_t carry = 0;
    for (size_t i = 0; i < reserved_digits + 1; ++i) {
        uint32_t lhs_digit = 0;
        if (i < lhs_length) {
            aws_array_list_get_at(&lhs->digits, &lhs_digit, i);
        }

        uint32_t rhs_digit = 0;
        if (i < rhs_length) {
            aws_array_list_get_at(&rhs->digits, &rhs_digit, i);
        }

        uint64_t sum = carry + (uint64_t)lhs_digit + (uint64_t)rhs_digit;
        uint32_t final_digit = (uint32_t)(sum & LOWER_32_BIT_MASK);
        carry = (sum > LOWER_32_BIT_MASK) ? 1 : 0;

        /* this is how we support aliasing */
        if (i >= output_length) {
            aws_array_list_push_back(&output->digits, &final_digit);
        } else {
            aws_array_list_set_at(&output->digits, &final_digit, i);
        }
    }

    s_aws_bigint_trim_leading_zeros(output);

    return AWS_OP_SUCCESS;
}

/*
 * Subtracts the smaller magnitude from the larger magnitude
 */
static int s_aws_bigint_subtract_magnitudes(
    struct aws_bigint *output,
    struct aws_bigint *lhs,
    struct aws_bigint *rhs,
    enum aws_bigint_ordering ordering) {

    if (ordering == AWS_BI_EQUAL_TO) {
        uint32_t zero = 0;
        aws_array_list_clear(&output->digits);
        aws_array_list_push_back(&output->digits, &zero);
        return AWS_OP_SUCCESS;
    }

    struct aws_bigint *larger = lhs;
    struct aws_bigint *smaller = rhs;
    if (ordering == AWS_BI_LESS_THAN) {
        larger = rhs;
        smaller = lhs;
    }

    size_t larger_length = aws_array_list_length(&larger->digits);
    size_t smaller_length = aws_array_list_length(&smaller->digits);
    AWS_FATAL_ASSERT(larger_length > 0);

    if (aws_array_list_ensure_capacity(&output->digits, larger_length - 1)) {
        return AWS_OP_ERR;
    }
    size_t output_length = aws_array_list_length(&output->digits);

    uint64_t borrow = 0;
    for (size_t i = 0; i < larger_length; ++i) {
        uint32_t larger_digit = 0;
        if (i < larger_length) {
            aws_array_list_get_at(&larger->digits, &larger_digit, i);
        }

        uint32_t smaller_digit = 0;
        if (i < smaller_length) {
            aws_array_list_get_at(&smaller->digits, &smaller_digit, i);
        }

        uint64_t difference = (uint64_t)larger_digit - (uint64_t)smaller_digit - borrow;
        uint32_t final_digit = (uint32_t)(difference & LOWER_32_BIT_MASK);
        borrow = (difference > LOWER_32_BIT_MASK) ? 1 : 0;

        /* this is how we support aliasing */
        if (i >= output_length) {
            aws_array_list_push_back(&output->digits, &final_digit);
        } else {
            aws_array_list_set_at(&output->digits, &final_digit, i);
        }
    }

    s_aws_bigint_trim_leading_zeros(output);

    return AWS_OP_SUCCESS;
}

int aws_bigint_add(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs) {
    /*
     * (1) Figure out what the sign should be
     * (2) Call either add or subtract (magnitudes) based on sign and magnitude comparison
     */
    if (lhs->sign == rhs->sign) {
        /* positive + positive or negative + negative */
        output->sign = lhs->sign;
        return s_aws_bigint_add_magnitudes(output, lhs, rhs);
    } else {
        /* mixed signs; the final sign is the sign of the operand with the larger magnitude */
        enum aws_bigint_ordering ordering = s_aws_bigint_get_magnitude_ordering(lhs, rhs);
        if (ordering == AWS_BI_GREATER_THAN) {
            output->sign = lhs->sign;
        } else if (ordering == AWS_BI_LESS_THAN) {
            output->sign = rhs->sign;
        } else {
            /* a + -a = 0, which by fiat we say has a positive sign */
            output->sign = 1;
        }

        return s_aws_bigint_subtract_magnitudes(output, lhs, rhs, ordering);
    }
}

int aws_bigint_subtract(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs) {
    /*
     * (1) Figure out what the sign should be
     * (2) Call either add or subtract (magnitudes) based on sign and magnitude comparison
     */
    if (lhs->sign != rhs->sign) {
        /* positive - negative or negative - positive */
        output->sign = lhs->sign;
        return s_aws_bigint_add_magnitudes(output, lhs, rhs);
    } else {
        /* same sign; the final sign is a function of the lhs's sign and whichever operand is bigger*/
        enum aws_bigint_ordering ordering = s_aws_bigint_get_magnitude_ordering(lhs, rhs);
        if (ordering == AWS_BI_GREATER_THAN) {
            output->sign = lhs->sign;
        } else if (ordering == AWS_BI_LESS_THAN) {
            output->sign = -lhs->sign;
        } else {
            /* a - a = 0, positive sign by fiat */
            output->sign = 1;
        }

        return s_aws_bigint_subtract_magnitudes(output, lhs, rhs, ordering);
    }
}
