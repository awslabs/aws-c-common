#ifndef AWS_COMMON_BIGNUM_H
#define AWS_COMMON_BIGNUM_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/byte_buf.h>

AWS_PUSH_SANE_WARNING_LEVEL

/**
 * Arbitrary-precision signed integer. The magnitude of every value is limited to 2048 bytes (256 64-bit words), that is
 * |v| < 2^16384, which is at most 4,933 decimal digits (but some numbers of that digit length are over magnitude).
 *
 * Big integers do not have arithmetic support, you can use aws_byte_buf_append_big_integer to export a value into
 * another library to do so.
 */
struct aws_big_integer;

/**
 * Arbitrary-precision decimal, with value = mantissa * 10^exponent. The mantissa is a big integer and the exponent is
 * an int64_t.
 *
 * Like big integer, big decimals do not have arithmetic support.
 */
struct aws_big_decimal;

AWS_EXTERN_C_BEGIN

/**
 * Creates a big integer from a sign and an unsigned big-endian magnitude. An empty cursor is zero, which is never
 * negative.
 *
 * Raises AWS_ERROR_INVALID_ARGUMENT when the input exceeds the word limit.
 */
AWS_COMMON_API
struct aws_big_integer *aws_big_integer_new(
    struct aws_allocator *allocator,
    struct aws_byte_cursor bytes,
    bool is_negative);

/**
 * Creates a big integer from its base-10 digit representation in cursor.
 *
 * Accepts grammar [ "-" / "+" ] 1*DIGIT
 *
 * Raises AWS_ERROR_INVALID_ARGUMENT on malformed input or when the input exceeds the digit limit.
 */
AWS_COMMON_API
struct aws_big_integer *aws_big_integer_new_from_cursor(struct aws_allocator *allocator, struct aws_byte_cursor cursor);

/**
 * Destroy the big integer.
 */
AWS_COMMON_API
void aws_big_integer_destroy(struct aws_big_integer *v);

/**
 * Appends the big integer magnitude to output buffer as big-endian bytes. Zero appends nothing. The sign is
 * not encoded.
 *
 * If the output buffer has an allocator it grows as needed. Otherwise it is a fixed buffer, and
 * AWS_ERROR_DEST_COPY_TOO_SMALL is raised if the bytes do not fit. The length of the output buffer is not modified on
 * failure.
 */
AWS_COMMON_API
int aws_big_integer_get_magnitude_be(const struct aws_big_integer *v, struct aws_byte_buf *out);

/**
 * Returns -1 when big integer is negative, 1 if positive, and 0 when zero.
 */
AWS_COMMON_API
int aws_big_integer_get_sign(const struct aws_big_integer *v);

/**
 * Check equality of two big integers.
 */
AWS_COMMON_API
bool aws_big_integer_eq(const struct aws_big_integer *a, const struct aws_big_integer *b);

/**
 * Returns an upper bound on the number of bytes needed to represent the big integer as a base-10 string, including the
 * leading '-' for negative value, without a null terminator. The length is a fast-computed estimate that exceeds the
 * actual number of bytes needed by at most 1.
 */
AWS_COMMON_API
size_t aws_big_integer_max_strlen(const struct aws_big_integer *v);

/**
 * Appends the base-10 representation to output buffer, without a null terminator.
 *
 * If the output buffer has an allocator it grows as needed. Otherwise it is a fixed buffer, and
 * AWS_ERROR_DEST_COPY_TOO_SMALL is raised if the string does not fit. The length of the output buffer is not modified
 * on failure.
 */
AWS_COMMON_API
int aws_byte_buf_append_big_integer(struct aws_byte_buf *out, const struct aws_big_integer *v);

/**
 * Creates a big decimal with value = mantissa * 10^exponent. The returned big decimal allocates a copy of the mantissa.
 */
AWS_COMMON_API
struct aws_big_decimal *aws_big_decimal_new(
    struct aws_allocator *allocator,
    const struct aws_big_integer *mantissa,
    int64_t exponent);

/**
 * Parses a base-10 big decimal from input cursor.
 *
 * Accepts grammar [ "-" / "+" ] 1*DIGIT [ "." 1*DIGIT ] [ "e" [ "-" / "+" ] 1*DIGIT ]
 *
 * Raises AWS_ERROR_INVALID_ARGUMENT if the input is malformed or the mantissa exceeds the digit limit.
 * Raises AWS_ERROR_OVERFLOW_DETECTED if the exponent does not fit in int64_t.
 */
AWS_COMMON_API
struct aws_big_decimal *aws_big_decimal_new_from_cursor(struct aws_allocator *allocator, struct aws_byte_cursor cursor);

/**
 * Destroy the big decimal.
 */
AWS_COMMON_API
void aws_big_decimal_destroy(struct aws_big_decimal *v);

/**
 * Returns the mantissa. The result is owned by the big decimal and is valid until the big decimal is destroyed. Do not
 * pass it to aws_big_integer_destroy.
 */
AWS_COMMON_API
const struct aws_big_integer *aws_big_decimal_get_mantissa(const struct aws_big_decimal *v);

/**
 * Returns the exponent.
 */
AWS_COMMON_API
int64_t aws_big_decimal_get_exponent(const struct aws_big_decimal *v);

/**
 * Check equality of two big decimals. This compares the representation, not the numeric value: the mantissas and the
 * exponents must both be equal, so 150e-2 is not equal to 15e-1, and 15e1 is not equal to 150e0.
 */
AWS_COMMON_API
bool aws_big_decimal_eq(const struct aws_big_decimal *a, const struct aws_big_decimal *b);

/**
 * Returns an upper bound on the number of bytes needed to represent the big decimal as a base-10 string with
 * aws_byte_buf_append_big_decimal(), without a null terminator. The length is a fast-computed estimate that exceeds the
 * actual number of bytes needed by at most 1.
 */
AWS_COMMON_API
size_t aws_big_decimal_max_strlen(const struct aws_big_decimal *v);

/**
 * Appends the base-10 representation to output buffer, without a null terminator.
 *
 * The output is '[-]<mantissa digits>e[-]<exponent>'.
 *
 * If the output buffer has an allocator it grows as needed. Otherwise it is a fixed buffer, and
 * AWS_ERROR_DEST_COPY_TOO_SMALL is raised if the string does not fit. The length of the output buffer is not modified
 * on failure.
 */
AWS_COMMON_API
int aws_byte_buf_append_big_decimal(struct aws_byte_buf *out, const struct aws_big_decimal *v);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif /* AWS_COMMON_BIGNUM_H */
