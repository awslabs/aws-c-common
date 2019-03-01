/*
 * Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/*
 * This header is already included, but include it again to make editor
 * highlighting happier.
 */
#include <aws/common/common.h>

/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_mul_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t x = a * b;
    if (a != 0 && (a > UINT32_MAX || b > UINT32_MAX) && x / a != b) {
        return UINT64_MAX;
    }
    return x;
}

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint64_t x = a * b;
    *r = x;
    if (a != 0 && (a > UINT32_MAX || b > UINT32_MAX) && x / a != b) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_mul_u32_saturating(uint32_t a, uint32_t b) {
    uint32_t x = a * b;
    if (a != 0 && (a > UINT16_MAX || b > UINT16_MAX) && x / a != b) {
        return UINT32_MAX;
    }
    return x;
}

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    uint32_t x = a * b;
    *r = x;
    if (a != 0 && (a > UINT16_MAX || b > UINT16_MAX) && x / a != b) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b.  If the result overflows returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_add_u64_saturating(uint64_t a, uint64_t b) {
    uint64_t x = a + b;
    if (x < a) {
        return UINT64_MAX;
    }
    return x;
}

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    uint64_t x = a + b;
    *r = x;
    if (x < a) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b. If the result overflows returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_add_u32_saturating(uint32_t a, uint32_t b) {
    uint32_t x = a + b;
    if (x < a) {
        return UINT32_MAX;
    }
    return x;
}

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    uint32_t x = a + b;
    *r = x;
    if (x < a) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}
