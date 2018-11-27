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

#if defined(AWS_HAVE_GCC_OVERFLOW_MATH_EXTENSIONS)
#    include <aws/common/math.gcc_overflow.inl>
#elif defined(__x86_64__) && defined(AWS_HAVE_GCC_INLINE_ASM)
#    include <aws/common/math.gcc_x64_asm.inl>
#elif defined(AWS_HAVE_MSVC_MULX)
#    include <aws/common/math.msvc.inl>
#else
#    include <aws/common/math.fallback.inl>
#endif

#if _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4127) /*Disable "conditional expression is constant" */
#endif                              /* _MSC_VER */

AWS_STATIC_IMPL size_t aws_mul_size_saturating(size_t a, size_t b) {
    /* static assert: SIZE_MAX == (~(uint32_t)0) || (~(uint64_t)0)*/
    char assert_sizet_is_32_or_64_bit
        [(((uint64_t)SIZE_MAX == ~(uint32_t)0) || ((uint64_t)SIZE_MAX == ~(uint64_t)0)) ? 1 : -1] = {0};
    /* suppress unused variable warning */
    (void)assert_sizet_is_32_or_64_bit;

    if ((uint64_t)SIZE_MAX == ~(uint32_t)0) {
        return (size_t)aws_mul_u32_saturating((uint32_t)a, (uint32_t)b);
    }
    return (size_t)aws_mul_u64_saturating(a, b);
}

AWS_STATIC_IMPL int aws_mul_size_checked(size_t a, size_t b, size_t *r) {
    if ((uint64_t)SIZE_MAX == ~(uint32_t)0) {
        return (int)aws_mul_u32_checked((uint32_t)a, (uint32_t)b, (uint32_t *)r);
    }
    return (int)aws_mul_u64_checked((uint32_t)a, (uint32_t)b, (uint64_t *)r);
}

#if _MSC_VER
#    pragma warning(pop)
#endif /* _MSC_VER */

#endif /* AWS_COMMON_MATH_H */
