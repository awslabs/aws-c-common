#ifndef AWS_COMMON_BIGINT_H
#define AWS_COMMON_BIGINT_H

/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/common.h>

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>

/*
 * Arbitrary-size integer type.
 *
 * The first version had no constant-time implementations.  Since then, some operations have been moved to
 * constant-time -- in particular, comparison and most constructors.
 */
struct aws_bigint;

enum aws_ordering {
    AWS_ORDERING_LT = -1,
    AWS_ORDERING_EQ = 0,
    AWS_ORDERING_GT = 1,
};

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_bigint_destroy(struct aws_bigint *bigint);

/**
 * Creates a zero-valued bigint
 * If desired_bit_width is zero, then the internal representation uses the minimum number of digits necessary
 *
 * Constant time as a function of desired_bit_width
 */
AWS_COMMON_API
struct aws_bigint *aws_bigint_new_zero(struct aws_allocator *allocator, size_t desired_bit_width);

/**
 * Creates a one-valued bigint
 * If desired_bit_width is zero, then the internal representation uses the minimum number of digits necessary
 *
 * Constant time as a function of desired_bit_width
 */
AWS_COMMON_API
struct aws_bigint *aws_bigint_new_one(struct aws_allocator *allocator, size_t desired_bit_width);

/**
 * Creates a big int from a string of hex digits.  String may start with "0x".  Leading zeros are skipped.
 * An empty string is considered an error.  A leading (-) symbol is not supported.  Use aws_bigint_negate() after
 * calling aws_bigint_new_from_hex_cursor() to generate an arbitrary negative number.
 *
 * If desired_bit_width is zero, then the internal representation uses the minimum number of digits necessary.
 * If desired_bit_width is positive and (when rounding up based on the internal digit representation) is insufficient
 * to hold the resulting number, NULL is returned.
 */
AWS_COMMON_API
struct aws_bigint *aws_bigint_new_from_hex_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor hex_digits,
    size_t desired_bit_width);

/**
 * Creates a big int from a sequence of bytes
 *
 * If desired_bit_width is zero, then the internal representation uses the minimum number of digits.
 * If desired_bit_width is positive and (when rounding up based on the internal digit representation) is insufficient
 * to hold the resulting number, NULL is returned.
 *
 * Constant time as a function of desired_bit_width and source cursor length
 */
AWS_COMMON_API
struct aws_bigint *aws_bigint_new_from_binary_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor source,
    size_t desired_bit_width);

/**
 * Creates a big int as a copy of another big int
 */
AWS_COMMON_API
struct aws_bigint *aws_bigint_new_clone(struct aws_allocator *allocator, const struct aws_bigint *source);

/**
 * Writes a bigint to a buffer as a hexadecimal number.  Will prepend (-) in front of negative numbers for
 * easier testing.  This API is primarily intended for testing.  Actual output (to various formats/bases) is TBD.
 */
AWS_COMMON_API
int aws_bigint_bytebuf_append_as_hex(const struct aws_bigint *bigint, struct aws_byte_buf *buffer);

/**
 * Writes a bigint to a buffer as a big endian sequence of octets.
 *
 * If desired_bit_width is non-zero, then leading zero-bytes will pad the output as necessary.  If desired_bit_width
 * is insufficient to hold the big-endian binary representation, only the lower desired_bit_width bits will be
 * written.
 * If desired_bit_width is zero only the minimum number of bytes will be written.
 */
AWS_COMMON_API
int aws_bigint_bytebuf_append_as_big_endian(
    const struct aws_bigint *bigint,
    struct aws_byte_buf *buffer,
    size_t desired_bit_width);

/**
 * Returns true if this integer is negative, false otherwise.
 *
 * Constant time
 */
AWS_COMMON_API
bool aws_bigint_is_negative(const struct aws_bigint *bigint);

/**
 * Returns true if this integer is positive, false otherwise.
 *
 * Constant time
 */
AWS_COMMON_API
bool aws_bigint_is_positive(const struct aws_bigint *bigint);

/**
 * Returns true if this integer is zero, false otherwise.
 *
 * Constant time
 */
AWS_COMMON_API
bool aws_bigint_is_zero(const struct aws_bigint *bigint);

/**
 * Negates the supplied bigint.  Has no effect on a zero-valued integer.
 *
 * Constant time
 */
AWS_COMMON_API
void aws_bigint_negate(struct aws_bigint *bigint);

/**
 * Compares two bigints and returns their relative ordering.
 *
 * Constant time as a function of the lengths of lhs and rhs
 */
AWS_COMMON_API
enum aws_ordering aws_bigint_compare(const struct aws_bigint *lhs, const struct aws_bigint *rhs);

/*
 * Adds two big integers, placing the result in output.  Output must have been initialized first.  Output
 * may alias to either operand.
 *
 * Constant time as a function of the lengths if the signs match.
 */
AWS_COMMON_API
int aws_bigint_add(struct aws_bigint *output, const struct aws_bigint *lhs, const struct aws_bigint *rhs);

/*
 * Subtracts two big integers, placing the result in output.  Output must have been initialized first.  Output
 * may alias to either operand (aliasing to the second is weird but not forbidden).
 */
AWS_COMMON_API
int aws_bigint_subtract(struct aws_bigint *output, const struct aws_bigint *lhs, const struct aws_bigint *rhs);

/*
 * Multiplies two big integers, placing the result in output.  Output must have been initialized first.  Output
 * may alias to either operand.
 */
AWS_COMMON_API
int aws_bigint_multiply(struct aws_bigint *output, const struct aws_bigint *lhs, const struct aws_bigint *rhs);

/*
 * Performs a right bit-shift on a big int, equivalently dividing by a power of two.
 */
AWS_COMMON_API
void aws_bigint_shift_right(struct aws_bigint *bigint, size_t shift_amount);

/*
 * Performs a left bit-shift on a big int, equivalently multiplying by a power of two.
 */
AWS_COMMON_API
int aws_bigint_shift_left(struct aws_bigint *bigint, size_t shift_amount);

/*
 * Divides two *non-negative* big integers, computing both the quotient and the remainder.  Quotient and remainder
 * must already be initialized.  Quotient and remainder may alias to operands but not to each other.
 */
AWS_COMMON_API
int aws_bigint_divide(
    struct aws_bigint *quotient,
    struct aws_bigint *remainder,
    const struct aws_bigint *lhs,
    const struct aws_bigint *rhs);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_BIGINT_H */
