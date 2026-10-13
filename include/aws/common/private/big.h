#ifndef AWS_COMMON_PRIVATE_BIG_H
#define AWS_COMMON_PRIVATE_BIG_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

/*
 * Largest magnitude, in bytes, that an aws_big_integer can hold: 512 64-bit words, so |v| < 2^32768. Callers that
 * decode untrusted input can use this to reject oversized data before allocating.
 */
enum { AWS_BIG_INTEGER_MAX_BYTES = 4096 };

#endif /* AWS_COMMON_PRIVATE_BIG_H */
