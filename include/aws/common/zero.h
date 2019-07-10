#ifndef AWS_COMMON_ZERO_H
#define AWS_COMMON_ZERO_H

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

#include <aws/common/stdbool.h>

#include <string.h>

/**
 * Set each byte in the struct to zero.
 */
#define AWS_ZERO_STRUCT(object)                                                                                        \
    do {                                                                                                               \
        memset(&(object), 0, sizeof(object));                                                                          \
    } while (0)

/**
 * Set each byte in the array to zero.
 */
#define AWS_ZERO_ARRAY(array)                                                                                          \
    do {                                                                                                               \
        memset((void *)array, 0, sizeof(array));                                                                       \
    } while (0)

/**
 * Returns whether each byte in the object is zero.
 */
#define AWS_IS_ZEROED(object) aws_is_zeroed(&(object), sizeof(object))

/**
 * Returns whether each byte is zero.
 */
AWS_STATIC_IMPL
bool aws_is_zeroed(const void *buf, size_t bufsize) {
    /* Optimization idea: vectorized instructions to check more than 64 bits at a time. */

    /* Check 64 bits at a time, then update buf to where u64 checks left off */
    const size_t num_u64_checks = bufsize / 8;
    const uint64_t *buf_u64 = buf;
    for (size_t i = 0; i < num_u64_checks; ++i) {
        if (buf_u64[i]) {
            return false;
        }
    }

    buf = buf_u64 + num_u64_checks;
    bufsize = bufsize % 8;

    /* Check 8 bits at a time */
    const uint8_t *buf_u8 = buf;
    for (size_t i = 0; i < bufsize; ++i) {
        if (buf_u8[i]) {
            return false;
        }
    }

    return true;
}

AWS_EXTERN_C_BEGIN

/**
 * Securely zeroes a memory buffer. This function will attempt to ensure that
 * the compiler will not optimize away this zeroing operation.
 */
AWS_COMMON_API
void aws_secure_zero(void *pBuf, size_t bufsize);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_ZERO_H */
