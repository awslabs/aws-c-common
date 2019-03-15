#ifndef AWS_COMMON_MATH_H
#define AWS_COMMON_MATH_H

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

#include <aws/common/common.h>
#include <aws/common/config.h>

#include <stdlib.h>

#ifdef __cplusplus
extern "C" {
#endif

#if defined(AWS_HAVE_GCC_OVERFLOW_MATH_EXTENSIONS) && (defined(__clang__) || !defined(__cplusplus))
/*
 * GCC and clang have these super convenient overflow checking builtins...
 * but (in the case of GCC) they're only available when building C source.
 * We'll fall back to one of the other inlinable variants (or a non-inlined version)
 * if we are building this header on G++.
 */
#    include <aws/common/math.gcc_overflow.inl>
#elif defined(__x86_64__) && defined(AWS_HAVE_GCC_INLINE_ASM)
#    include <aws/common/math.gcc_x64_asm.inl>
#elif defined(AWS_HAVE_MSVC_MULX)
#    include <aws/common/math.msvc.inl>
#else
#    ifndef AWS_HAVE_GCC_OVERFLOW_MATH_EXTENSIONS
/* Fall back to the pure-C implementations */
#        include <aws/common/math.fallback.inl>
#    else
/*
 * We got here because we are building in C++ mode but we only support overflow extensions
 * in C mode. Because the fallback is _slow_ (involving a division), we'd prefer to make a
 * non-inline call to the fast C intrinsics.
 */

/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
AWS_COMMON_API uint64_t aws_mul_u64_saturating(uint64_t a, uint64_t b);

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_COMMON_API int aws_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r);

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
AWS_COMMON_API uint32_t aws_mul_u32_saturating(uint32_t a, uint32_t b);

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_COMMON_API int aws_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r);

/**
 * Adds a + b.  If the result overflows returns 2^64 - 1.
 */
AWS_COMMON_API uint64_t aws_add_u64_saturating(uint64_t a, uint64_t b);

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_COMMON_API int aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r);

/**
 * Adds a + b. If the result overflows returns 2^32 - 1.
 */
AWS_COMMON_API uint32_t aws_add_u32_saturating(uint32_t a, uint32_t b);

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_COMMON_API int aws_add_u32_checked(uint32_t a, uint32_t b, uint32_t *r);

#    endif
#endif

#if _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4127) /*Disable "conditional expression is constant" */
#endif                              /* _MSC_VER */

/**
 * Multiplies a * b. If the result overflows, returns SIZE_MAX.
 */
AWS_STATIC_IMPL size_t aws_mul_size_saturating(size_t a, size_t b) {
#if SIZE_MAX == UINT32_MAX
    return (size_t)aws_mul_u32_saturating(a, b);
#elif SIZE_MAX == UINT64_MAX
    return (size_t)aws_mul_u64_saturating(a, b);
#else
#    error "Target not supported"
#endif
}

/**
 * Multiplies a * b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_size_checked(size_t a, size_t b, size_t *r) {
#if SIZE_MAX == UINT32_MAX
    return aws_mul_u32_checked(a, b, (uint32_t *)r);
#elif SIZE_MAX == UINT64_MAX
    return aws_mul_u64_checked(a, b, (uint64_t *)r);
#else
#    error "Target not supported"
#endif
}

/**
 * Adds a + b.  If the result overflows returns SIZE_MAX.
 */
AWS_STATIC_IMPL size_t aws_add_size_saturating(size_t a, size_t b) {
#if SIZE_MAX == UINT32_MAX
    return (size_t)aws_add_u32_saturating(a, b);
#elif SIZE_MAX == UINT64_MAX
    return (size_t)aws_add_u64_saturating(a, b);
#else
#    error "Target not supported"
#endif
}

/**
 * Adds a + b and returns the result in *r. If the result
 * overflows, returns AWS_OP_ERR; otherwise returns AWS_OP_SUCCESS.
 */

AWS_STATIC_IMPL int aws_add_size_checked(size_t a, size_t b, size_t *r) {
#if SIZE_MAX == UINT32_MAX
    return aws_add_u32_checked(a, b, (uint32_t *)r);
#elif SIZE_MAX == UINT64_MAX
    return aws_add_u64_checked(a, b, (uint64_t *)r);
#else
#    error "Target not supported"
#endif
}

#if _MSC_VER
#    pragma warning(pop)
#endif /* _MSC_VER */

#ifdef __cplusplus
}
#endif

#endif /* AWS_COMMON_MATH_H */
