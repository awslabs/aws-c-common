#ifndef AWS_COMMON_MATH_GCC_BUILTIN_INL
#define AWS_COMMON_MATH_GCC_BUILTIN_INL

/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <aws/common/math.h>

/* clang-format off */

AWS_EXTERN_C_BEGIN

/**
 * Search from the MSB to LSB, looking for a 1
 */
AWS_STATIC_IMPL size_t aws_clz_u32(uint32_t n) {
    return __builtin_clzl(n);
}

AWS_STATIC_IMPL size_t aws_clz_i32(int32_t n) {
    return __builtin_clz(n);
}

AWS_STATIC_IMPL size_t aws_clz_u64(uint64_t n) {
    return __builtin_clzll(n);
}

AWS_STATIC_IMPL size_t aws_clz_i64(int64_t n) {
    return __builtin_clzll(n);
}

AWS_STATIC_IMPL size_t aws_clz_size(size_t n) {
#if SIZE_BITS == 64
    return aws_clz_u64(n);
#else
    return aws_clz_u32(n);
#endif
}

/**
 * Search from the LSB to MSB, looking for a 1
 */
AWS_STATIC_IMPL size_t aws_ctz_u32(uint32_t n) {
    return __builtin_ctzl(n);
}

AWS_STATIC_IMPL size_t aws_ctz_i32(int32_t n) {
    return __builtin_ctz(n);
}

AWS_STATIC_IMPL size_t aws_ctz_u64(uint64_t n) {
    return __builtin_ctzll(n);
}

AWS_STATIC_IMPL size_t aws_ctz_i64(int64_t n) {
    return __builtin_ctzll(n);
}

AWS_STATIC_IMPL size_t aws_ctz_size(size_t n) {
#if SIZE_BITS == 64
    return aws_ctz_u64(n);
#else
    return aws_ctz_u32(n);
#endif
}

AWS_EXTERN_C_END

/* clang-format on */

#endif /* AWS_COMMON_MATH_GCC_BUILTIN_INL */
