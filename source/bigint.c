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
#define DIVISION_NORMALIZATION_BIT_MASK (1U << (BASE_BITS - 1))

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
    AWS_ZERO_STRUCT(bigint->digits);
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

static int s_aws_bigint_init_zero(struct aws_bigint *bigint, struct aws_allocator *allocator, size_t reserved_digits) {
    size_t reserved = reserved_digits > 0 ? reserved_digits : 1;
    if (aws_array_list_init_dynamic(&bigint->digits, allocator, reserved, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    uint32_t zero_digit = 0;
    for (size_t i = 0; i < reserved; ++i) {
        aws_array_list_push_back(&bigint->digits, &zero_digit);
    }

    bigint->sign = 1;

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

    size_t digit_count = (hex_digits.len - 1) / NIBBLES_PER_DIGIT + 1;
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
    size_t digit_count = upper_digit > 0 ? 2 : 1;
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
    size_t max_hex_digits = aws_array_list_length(&bigint->digits) * NIBBLES_PER_DIGIT;
    size_t total_characters = max_hex_digits + ((bigint->sign < 0) ? 1 : 0);
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

/*
 * Either succeeds or makes no change to the output
 */
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
 * Subtracts the smaller magnitude from the larger magnitude.
 * Either succeeds or makes no (visible) change to output
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
    int output_sign = 1;
    if (lhs->sign == rhs->sign) {
        /* positive + positive or negative + negative */
        output_sign = lhs->sign;
        if (s_aws_bigint_add_magnitudes(output, lhs, rhs)) {
            return AWS_OP_ERR;
        }
    } else {
        /* mixed signs; the final sign is the sign of the operand with the larger magnitude */
        enum aws_bigint_ordering ordering = s_aws_bigint_get_magnitude_ordering(lhs, rhs);
        if (ordering == AWS_BI_GREATER_THAN) {
            output_sign = lhs->sign;
        } else if (ordering == AWS_BI_LESS_THAN) {
            output_sign = rhs->sign;
        } /* else a + -a = 0, which by fiat we say has a positive sign, so do nothing */

        if (s_aws_bigint_subtract_magnitudes(output, lhs, rhs, ordering)) {
            return AWS_OP_ERR;
        }
    }

    output->sign = output_sign;

    return AWS_OP_SUCCESS;
}

int aws_bigint_subtract(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs) {
    /*
     * (1) Figure out what the sign should be
     * (2) Call either add or subtract (magnitudes) based on sign and magnitude comparison
     */
    int output_sign = 1;
    if (lhs->sign != rhs->sign) {
        /* positive - negative or negative - positive */
        output_sign = lhs->sign;
        if (s_aws_bigint_add_magnitudes(output, lhs, rhs)) {
            return AWS_OP_ERR;
        }
    } else {
        /* same sign; the final sign is a function of the lhs's sign and whichever operand is bigger*/
        enum aws_bigint_ordering ordering = s_aws_bigint_get_magnitude_ordering(lhs, rhs);
        if (ordering == AWS_BI_GREATER_THAN) {
            output_sign = lhs->sign;
        } else if (ordering == AWS_BI_LESS_THAN) {
            output_sign = -lhs->sign;
        } /* else a - a = 0, positive sign by fiat, so do nothing */

        if (s_aws_bigint_subtract_magnitudes(output, lhs, rhs, ordering)) {
            return AWS_OP_ERR;
        }
    }

    output->sign = output_sign;

    return AWS_OP_SUCCESS;
}

int aws_bigint_multiply(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs) {
    struct aws_bigint temp_output;
    AWS_ZERO_STRUCT(temp_output);

    struct aws_allocator *allocator = output->digits.alloc;

    size_t lhs_length = aws_array_list_length(&lhs->digits);
    size_t rhs_length = aws_array_list_length(&rhs->digits);
    size_t digit_count_sum = lhs_length + rhs_length;

    if (aws_array_list_ensure_capacity(&output->digits, digit_count_sum)) {
        return AWS_OP_ERR;
    }

    if (aws_array_list_init_dynamic(&temp_output.digits, allocator, digit_count_sum, sizeof(uint32_t))) {
        return AWS_OP_ERR;
    }

    /*
     * No way to fail beyond this point
     */

    /*
     * Pad with sufficient zeros to cover all possible digits that could be non zero in the final product
     * We do this so that when we add the current product digit into the accumulating product, there's already
     * a value there (0).  We could conditionally retrieve it too, but this keeps us from having to add
     * if-then checks around both the read and the write.
     */
    for (size_t i = 0; i < digit_count_sum; ++i) {
        uint32_t zero = 0;
        aws_array_list_push_back(&temp_output.digits, &zero);
    }

    for (size_t i = 0; i < lhs_length; ++i) {
        uint32_t lhs_digit = 0;
        aws_array_list_get_at(&lhs->digits, &lhs_digit, i);

        /* Multiply "lhs_digit * rhs" and add into temp_output at the appropriate offset */
        uint64_t carry = 0;
        for (size_t j = 0; j < rhs_length; ++j) {
            uint32_t rhs_digit = 0;
            aws_array_list_get_at(&rhs->digits, &rhs_digit, j);

            uint32_t output_digit = 0;
            aws_array_list_get_at(&temp_output.digits, &output_digit, i + j);

            /* multiply-and-add a single digit pair */
            uint64_t product_digit = (uint64_t)lhs_digit * (uint64_t)rhs_digit + carry + (uint64_t)output_digit;
            uint32_t final_product_digit = (uint32_t)(product_digit & LOWER_32_BIT_MASK);
            carry = (product_digit >> 32);

            aws_array_list_set_at(&temp_output.digits, &final_product_digit, i + j);
        }

        if (carry > 0) {
            uint32_t carry_digit = (uint32_t)carry; /* safe */
            /* we can set_at here because we know the existing value must be zero */
            aws_array_list_set_at(&temp_output.digits, &carry_digit, i + rhs_length);
        }
    }

    s_aws_bigint_trim_leading_zeros(&temp_output);

    if ((lhs->sign == rhs->sign) || aws_bigint_is_zero(&temp_output)) {
        output->sign = 1;
    } else {
        output->sign = -1;
    }

    aws_array_list_swap_contents(&temp_output.digits, &output->digits);

    aws_bigint_clean_up(&temp_output);

    return AWS_OP_SUCCESS;
}

/* this function can't fail */
void aws_bigint_shift_right(struct aws_bigint *bigint, size_t shift_amount) {
    size_t digit_count = aws_array_list_length(&bigint->digits);

    /*
     * Break the shift into two parts:
     *  (1) base_shift_count = whole digit shifts (shift_amount / BASE_BITS)
     *  (2) bit_shift_count = leftover amount (shift_amount % BASE_BITS), 0 <= bit_shifts < BASE_BITS
     */
    size_t base_shift_count = shift_amount / BASE_BITS;
    uint32_t bit_shift_count = (uint32_t)(shift_amount % BASE_BITS);

    /* is it guaranteed to be zero? */
    if (base_shift_count >= digit_count) {
        aws_array_list_clear(&bigint->digits);

        uint32_t zero_digit = 0;
        aws_array_list_push_back(&bigint->digits, &zero_digit);
        bigint->sign = 1;
        return;
    }

    /* move whole digits base_shift_count places.  This could be replaced by a memmove but that seems sketchy. */
    if (base_shift_count > 0) {
        size_t copy_count = digit_count - base_shift_count;

        for (size_t i = 0; i < copy_count; ++i) {
            uint32_t source_digit = 0;
            aws_array_list_get_at(&bigint->digits, &source_digit, i + base_shift_count);
            aws_array_list_set_at(&bigint->digits, &source_digit, i);
        }

        /* pop base_shift_count digits from the end */
        for (size_t i = 0; i < base_shift_count; i++) {
            aws_array_list_pop_back(&bigint->digits);
        }
    }

    /* now do a bit shift for the remaining amount */
    if (bit_shift_count > 0) {

        /* how many digits are left? */
        digit_count = digit_count - base_shift_count;

        /* shifts and masks to build the new digits */
        uint32_t low_mask = (1U << bit_shift_count) - 1;
        uint32_t high_shift = (BASE_BITS - bit_shift_count);

        /* loop from low to high, shifting down and bringing in the appropriate bits from the next digit */
        uint32_t current_digit = 0;
        aws_array_list_get_at(&bigint->digits, &current_digit, 0);
        for (size_t i = 0; i < digit_count; ++i) {
            uint32_t next_digit = 0;
            if (i + 1 < digit_count) {
                aws_array_list_get_at(&bigint->digits, &next_digit, i + 1);
            }

            current_digit >>= bit_shift_count;
            uint32_t new_current_high_bits = (next_digit & low_mask) << high_shift;

            uint32_t final_digit = current_digit | new_current_high_bits;
            aws_array_list_set_at(&bigint->digits, &final_digit, i);

            current_digit = next_digit;
        }
    }

    s_aws_bigint_trim_leading_zeros(bigint);
}

int aws_bigint_shift_left(struct aws_bigint *bigint, size_t shift_amount) {

    size_t digit_count = aws_array_list_length(&bigint->digits);

    /*
     * Break the shift into two parts:
     *  (1) base_shift_count = while digit copies (shift_amount / BASE_BITS)
     *  (2) bit_shift_count = remainder (shift_amount % BASE_BITS), 0 <= bit_shifts < BASE_BITS
     */
    size_t base_shift_count = shift_amount / BASE_BITS;
    uint32_t bit_shift_count = (uint32_t)(shift_amount % BASE_BITS);

    /* I hate this API, technically we're reserving (digit_count + base_shift_count + 1) */
    if (aws_array_list_ensure_capacity(&bigint->digits, digit_count + base_shift_count)) {
        return AWS_OP_ERR;
    }

    /* can't fail beyond this point */

    /* do the bit_shift_count part first */
    if (bit_shift_count > 0) {
        uint32_t high_shift = BASE_BITS - bit_shift_count;
        uint32_t low_bits = 0;
        for (size_t i = 0; i < digit_count; ++i) {
            uint32_t current_digit = 0;
            aws_array_list_get_at(&bigint->digits, &current_digit, i);

            uint32_t final_digit = (current_digit << bit_shift_count) | low_bits;
            aws_array_list_set_at(&bigint->digits, &final_digit, i);

            low_bits = current_digit >> high_shift;
        }

        if (low_bits > 0) {
            aws_array_list_push_back(&bigint->digits, &low_bits);
        }
    }

    /* do the multiple of 32 bit shift part by copying */
    if (base_shift_count > 0) {
        /* first push enough placeholder zeroes on to the end */
        for (size_t i = 0; i < base_shift_count; ++i) {
            uint32_t zero_digit = 0;
            aws_array_list_push_back(&bigint->digits, &zero_digit);
        }

        digit_count = aws_array_list_length(&bigint->digits);

        /* high to low, copy whole digits base_shift_count places apart, writing zeros appropriately */
        for (size_t i = 0; i < digit_count; ++i) {
            size_t dest_index = digit_count - i - 1;
            uint32_t source_digit = 0;
            if (dest_index >= base_shift_count) {
                aws_array_list_get_at(&bigint->digits, &source_digit, dest_index - base_shift_count);
            }

            aws_array_list_set_at(&bigint->digits, &source_digit, dest_index);
        }
    }

    s_aws_bigint_trim_leading_zeros(bigint);

    return AWS_OP_SUCCESS;
}

/*
 * Division
 */

/*
 * The basic, general algorithm for bigint division requires a divisor to be at least two digits in order for its
 * quotient digit calculations to be mathematically accurate.  This isn't a big deal since it turns out division by
 * a single-digit divisor is pretty easy.  That special case is handled here.
 */
static int s_aws_bigint_divide_by_single_digit(
    struct aws_bigint *quotient,
    struct aws_bigint *remainder,
    const struct aws_bigint *dividend,
    uint32_t divisor) {

    struct aws_bigint temp_quotient;
    size_t quotient_length = aws_array_list_length(&dividend->digits);

    if (s_aws_bigint_init_zero(&temp_quotient, quotient->digits.alloc, quotient_length)) {
        return AWS_OP_ERR;
    }

    uint64_t wide_divisor = divisor;
    uint64_t current_remainder = 0;
    for (size_t i = 0; i < quotient_length; ++i) {

        /* highest order to lowest order digit */
        uint32_t current_dividend_digit = 0;
        aws_array_list_get_at(&dividend->digits, &current_dividend_digit, quotient_length - 1 - i);

        uint64_t two_digit_dividend = (current_remainder << BASE_BITS) + current_dividend_digit;

        uint32_t quotient_digit = (uint32_t)(two_digit_dividend / wide_divisor);
        aws_array_list_set_at(&temp_quotient.digits, &quotient_digit, quotient_length - 1 - i);

        current_remainder = two_digit_dividend % wide_divisor;
    }

    s_aws_bigint_trim_leading_zeros(&temp_quotient);

    aws_array_list_swap_contents(&temp_quotient.digits, &quotient->digits);
    quotient->sign = 1;

    uint32_t final_remainder = (uint32_t)current_remainder;
    aws_array_list_clear(&remainder->digits);
    aws_array_list_push_back(&remainder->digits, &final_remainder);
    remainder->sign = 1;

    aws_bigint_clean_up(&temp_quotient);

    return AWS_OP_SUCCESS;
}

/*
 * The general division algorithm requires the divisor to be at least half the base.  In our implementation we shift
 * the operands left (x 2) until the divisor's high bit is set.
 */
static uint32_t s_compute_divisor_normalization_shift(const struct aws_bigint *bigint) {
    size_t digit_count = aws_array_list_length(&bigint->digits);
    AWS_FATAL_ASSERT(digit_count > 0);

    uint32_t high_digit = 0;
    aws_array_list_get_at(&bigint->digits, &high_digit, digit_count - 1);
    AWS_FATAL_ASSERT(high_digit > 0);

    uint32_t shift_count = 0;
    while ((high_digit & DIVISION_NORMALIZATION_BIT_MASK) == 0) {
        high_digit <<= 1;
        ++shift_count;
    }

    return shift_count;
}

/*
 * General algorithm requirements/assumptions:
 *   (1) lhs >= rhs
 *   (2) lhs, rhs both positive
 *   (3) rhs is at least two digits in length
 *   (4) lhs, rhs have been normalized so that rhs's high order digit has the high bit set
 *   (5) lhs is at least one digit longer than rhs
 *
 * Additional points:
 *   (1) lhs may have a leading zero digit
 *
 * Side effects:
 *   (1) lhs is destructively modified to the remainder and then swapped with the remainder
 *
 * Implementation based on Algorithm D, steps D2 - D7, in section 4.3.1 of AoCP Vol 2.
 * Steps D1, D8 are performed by the caller.
 */
static int s_aws_bigint_normalized_divide(
    struct aws_bigint *quotient,
    struct aws_bigint *remainder,
    struct aws_bigint *lhs,
    const struct aws_bigint *rhs) {

    size_t lhs_digit_count = aws_array_list_length(&lhs->digits);
    size_t rhs_digit_count = aws_array_list_length(&rhs->digits);
    AWS_FATAL_ASSERT(lhs_digit_count > rhs_digit_count); /* padding by zero */
    AWS_FATAL_ASSERT(rhs_digit_count >= 2);

    size_t quotient_digit_count = lhs_digit_count - rhs_digit_count;

    if (s_aws_bigint_init_zero(quotient, lhs->digits.alloc, quotient_digit_count) ||
        aws_bigint_init_from_uint64(remainder, lhs->digits.alloc, 0)) {
        return AWS_OP_ERR;
    }

    uint32_t divisor_high_digit = 0;
    aws_array_list_get_at(&rhs->digits, &divisor_high_digit, rhs_digit_count - 1);

    uint32_t divisor_almost_high_digit = 0;
    aws_array_list_get_at(&rhs->digits, &divisor_almost_high_digit, rhs_digit_count - 2);

    uint64_t base = 1ULL << BASE_BITS;

    for (size_t i = 0; i < quotient_digit_count; ++i) {
        size_t lhs_index = lhs_digit_count - i - 1;

        AWS_FATAL_ASSERT(lhs_index >= 2);

        uint32_t highest_digit = 0;
        uint32_t second_highest_digit = 0;
        uint32_t third_highest_digit = 0;
        aws_array_list_get_at(&lhs->digits, &highest_digit, lhs_index);
        aws_array_list_get_at(&lhs->digits, &second_highest_digit, lhs_index - 1);
        aws_array_list_get_at(&lhs->digits, &third_highest_digit, lhs_index - 2);

        /* D3 - Calculate q_hat */
        uint64_t q_dividend = ((uint64_t)highest_digit << BASE_BITS) + (uint64_t)second_highest_digit;
        uint64_t q_guess = q_dividend / (uint64_t)divisor_high_digit;
        uint64_t r_guess = q_dividend % (uint64_t)divisor_high_digit;

        while (q_guess >= base || q_guess * divisor_almost_high_digit > base * r_guess + third_highest_digit) {
            --q_guess;
            r_guess += divisor_high_digit;
            if (r_guess >= base) {
                break;
            }
        }

        /* D4 - Multiply and subtract */
        uint64_t borrow = 0;
        for (size_t j = 0; j < rhs_digit_count + 1; ++j) {
            uint32_t divisor_digit = 0;
            if (j < rhs_digit_count) {
                aws_array_list_get_at(&rhs->digits, &divisor_digit, j);
            }

            uint32_t current_digit = 0;
            aws_array_list_get_at(&lhs->digits, &current_digit, lhs_index - rhs_digit_count + j);

            uint64_t product_digit = q_guess * divisor_digit;

            uint64_t difference = (uint64_t)current_digit - product_digit - borrow;

            current_digit = (uint32_t)(difference & LOWER_32_BIT_MASK);
            borrow = (base - (difference >> BASE_BITS)) & LOWER_32_BIT_MASK;

            aws_array_list_set_at(&lhs->digits, &current_digit, lhs_index - rhs_digit_count + j);
        }

        /* D5,6 - If remainder negative perform add back step */
        if (borrow > 0) {
            --q_guess;
            uint64_t carry = 0;
            for (size_t j = 0; j < rhs_digit_count + 1; ++j) {
                uint32_t divisor_digit = 0;
                if (j < rhs_digit_count) {
                    aws_array_list_get_at(&rhs->digits, &divisor_digit, j);
                }

                uint32_t current_digit = 0;
                aws_array_list_get_at(&lhs->digits, &current_digit, lhs_index - rhs_digit_count + j);

                uint64_t digit_sum = (uint64_t)divisor_digit + (uint64_t)current_digit + carry;
                carry = digit_sum >> BASE_BITS;
                current_digit = (uint32_t)(digit_sum & LOWER_32_BIT_MASK);

                aws_array_list_set_at(&lhs->digits, &current_digit, lhs_index - rhs_digit_count + j);
            }

            AWS_FATAL_ASSERT(carry > 0);
        }

        uint32_t final_q = (uint32_t)q_guess;
        aws_array_list_set_at(&quotient->digits, &final_q, quotient_digit_count - i - 1);
    }

    /* copy the remainder which is currently in lhs */
    aws_array_list_clear(&remainder->digits);
    for (size_t i = 0; i < rhs_digit_count; ++i) {
        uint32_t remainder_digit = 0;
        aws_array_list_get_at(&lhs->digits, &remainder_digit, i);

        aws_array_list_push_back(&remainder->digits, &remainder_digit);
    }

    s_aws_bigint_trim_leading_zeros(quotient);
    s_aws_bigint_trim_leading_zeros(remainder);

    return AWS_OP_SUCCESS;
}

int aws_bigint_divide(
    struct aws_bigint *quotient,
    struct aws_bigint *remainder,
    const struct aws_bigint *lhs,
    const struct aws_bigint *rhs) {
    /* Step 1 - handle bad operands */
    if (aws_bigint_is_zero(rhs)) {
        return aws_raise_error(AWS_ERROR_DIVIDE_BY_ZERO);
    }

    /*
     * No negative numbers for now.
     *
     * Remove this restriction in the future, but right now this simplifies things.
     */
    if (aws_bigint_is_negative(lhs) || aws_bigint_is_negative(rhs)) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    /*
     * Step 2 - handle special cases:
     *   (1) Single digit divisor
     *   (2) Zero-valued quotient
     */

    /* single digit divisor */
    if (aws_array_list_length(&rhs->digits) == 1) {
        uint32_t digit = 0;
        aws_array_list_get_at(&rhs->digits, &digit, 0);
        return s_aws_bigint_divide_by_single_digit(quotient, remainder, lhs, digit);
    }

    int result = AWS_OP_ERR;

    struct aws_bigint temp_quotient;
    AWS_ZERO_STRUCT(temp_quotient);
    struct aws_bigint temp_remainder;
    AWS_ZERO_STRUCT(temp_remainder);
    struct aws_bigint normalized_lhs;
    AWS_ZERO_STRUCT(normalized_lhs);
    struct aws_bigint normalized_rhs;
    AWS_ZERO_STRUCT(normalized_rhs);

    if (aws_bigint_init_from_copy(&normalized_lhs, lhs)) {
        goto done;
    }

    /* handle zero-valued quotient */
    if (s_aws_bigint_get_magnitude_ordering(lhs, rhs) == AWS_BI_LESS_THAN) {
        /* can't fail from here on out, perform side effects */
        aws_array_list_swap_contents(&normalized_lhs.digits, &remainder->digits);
        remainder->sign = 1;

        aws_array_list_clear(&quotient->digits);

        uint32_t zero_digit = 0;
        aws_array_list_push_back(&quotient->digits, &zero_digit);
        quotient->sign = 1;

        result = AWS_OP_SUCCESS;
        goto done;
    }

    if (aws_bigint_init_from_copy(&normalized_rhs, rhs)) {
        goto done;
    }

    /* Step 3 - normalize lhs, rhs */
    /*
     * We normalize via bit shifting rather than arbitrary multiplication.  Normalization is the process where we
     * multiply both sides by a constant factor (here a power of 2) such that the divisor has its high bit set.  This
     * is equivalent to the requirement in AoCP 4.3.1 that the divisor's high digit is at least half the numeric base.
     *
     * Normalization enables our single digit quotient estimate to always be either exactly correct or 1 or 2 too large
     * regardless of the base used.
     */
    uint32_t normalization_shift = s_compute_divisor_normalization_shift(rhs);
    if (aws_bigint_shift_left(&normalized_lhs, normalization_shift)) {
        goto done;
    }

    /*
     * We add an empty zero high order digit because the algorithm works by estimating q based on the two highest
     * digits in the dividend.  But even after normalization, the two highest digits divided by the highest
     * digit in the divisor can still be wayyyy bigger than b.
     *
     * Consider 99 / 5 which is already normalized (base 10).  Clearly the first quotient digit should be based on 9/5
     * and not 99/5.  At the same time, 22 / 5 is already normalized, and clearly the first quotient digit should be
     * based on 22/5 and not 2/5.  At the same time, basing it on 2/5 doesn't hurt since it only ends up adding a
     * leading zero which will be trimmed in the end.
     *
     * So unconditionally adding a zero doesn't ever hurt, but corrects some cases.  "Incorrectly" adding a zero
     * causes us to run an extra iteration of the divide loop, yielding a leading zero on the quotient.
     *
     * TODO: make adding a leading zero properly conditional.
     */
    uint32_t zero_digit = 0;
    aws_array_list_push_back(&normalized_lhs.digits, &zero_digit);

    if (aws_bigint_shift_left(&normalized_rhs, normalization_shift)) {
        goto done;
    }

    /* Step 4 - divide */
    if (s_aws_bigint_normalized_divide(&temp_quotient, &temp_remainder, &normalized_lhs, &normalized_rhs)) {
        goto done;
    }

    /* Step 5 - quotient is correct, remainder is wack, so unnormalize remainder */
    aws_bigint_shift_right(&temp_remainder, normalization_shift);

    /* Step 6 - write to outputs */
    aws_array_list_swap_contents(&temp_quotient.digits, &quotient->digits);
    quotient->sign = 1;

    aws_array_list_swap_contents(&temp_remainder.digits, &remainder->digits);
    remainder->sign = 1;

    result = AWS_OP_SUCCESS;

done:

    aws_bigint_clean_up(&normalized_lhs);
    aws_bigint_clean_up(&normalized_rhs);
    aws_bigint_clean_up(&temp_quotient);
    aws_bigint_clean_up(&temp_remainder);

    return result;
}
