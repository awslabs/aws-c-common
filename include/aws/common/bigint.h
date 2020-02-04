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
 * A basic big integer implementation using 2^32 as the base.  Algorithms used are formalizations of the basic
 * grade school operations everyone knows and loves (as formalized in AoCP Vol 2, 4.3.1).  Current use case
 * targets do not yet involve a domain large enough that its worth exploring more complex algorithms.
 */
struct aws_bigint {
    /*
     * A sequence of base 2^32 digits starting from the least significant
     */
    struct aws_array_list digits;

    /*
     * 1 = positive, -1 = negative
     */
    int sign;
};

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_bigint_clean_up(struct aws_bigint *bigint);

AWS_COMMON_API
int aws_bigint_init_from_hex(
    struct aws_bigint *bigint,
    struct aws_allocator *allocator,
    struct aws_byte_cursor hex_digits);

AWS_COMMON_API
int aws_bigint_init_from_int64(struct aws_bigint *bigint, struct aws_allocator *allocator, int64_t value);

AWS_COMMON_API
int aws_bigint_init_from_uint64(struct aws_bigint *bigint, struct aws_allocator *allocator, uint64_t value);

AWS_COMMON_API
int aws_bigint_bytebuf_append_as_hex(struct aws_bigint *bigint, struct aws_byte_buf *buffer);

AWS_COMMON_API
bool aws_bigint_is_negative(struct aws_bigint *bigint);

AWS_COMMON_API
bool aws_bigint_is_positive(struct aws_bigint *bigint);

AWS_COMMON_API
bool aws_bigint_is_zero(struct aws_bigint *bigint);

AWS_COMMON_API
bool aws_bigint_equals(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
bool aws_bigint_not_equals(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
bool aws_bigint_less_than(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
bool aws_bigint_less_than_or_equals(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
bool aws_bigint_greater_than(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
bool aws_bigint_greater_than_or_equals(struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
void aws_bigint_negate(struct aws_bigint *bigint);

AWS_COMMON_API
int aws_bigint_add(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_COMMON_API
int aws_bigint_subtract(struct aws_bigint *output, struct aws_bigint *lhs, struct aws_bigint *rhs);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_BIGINT_H */
