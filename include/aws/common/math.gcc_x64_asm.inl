#ifndef AWS_COMMON_MATH_GCC_X64_ASM_INL
#define AWS_COMMON_MATH_GCC_X64_ASM_INL

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
#include <aws/common/math.h>

/* clang-format off */

AWS_EXTERN_C_BEGIN

/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_mul_u64_saturating(uint64_t a, uint64_t b) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86.

    we specify rdx as an output, rather than a clobber, because we want to
    allow it to be allocated as an input register */

    uint64_t rdx;
    __asm__("mulq %q[arg2]\n" /* rax * b, result is in RDX:RAX, OF=CF=(RDX != 0) */
            "cmovc %q[saturate], %%rax\n"
            : /* in/out: %rax = a, out: rdx (ignored) */ "+&a"(a), "=&d"(rdx)
            : /* in: register only */ [arg2] "r"(b),
              /* in: saturation value (reg/memory) */ [saturate] "rm"(~0LL)
            : /* clobbers: cc */ "cc");
    (void)rdx; /* suppress unused warnings */
    return a;
}

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */

    char flag;
    uint64_t result = a;
    __asm__("mulq %q[arg2]\n" /* rax * b, result is in RDX:RAX, OF=CF=(RDX != 0) */
            "seto %[flag]\n"  /* flag = overflow_bit */
            : /* in/out: %rax (first arg & result), %d (flag) */ "+&a"(result), [flag] "=&d"(flag)
            : /* in: reg for 2nd operand */
            [arg2] "r"(b)
            : /* clobbers: cc (d is used for flag so no need to clobber)*/ "cc");
    *r = result;
    if (flag) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_mul_u32_saturating(uint32_t a, uint32_t b) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86.

     we specify edx as an output, rather than a clobber, because we want to
    allow it to be allocated as an input register */
    uint32_t edx;
    __asm__("mull %k[arg2]\n" /* eax * b, result is in EDX:EAX, OF=CF=(EDX != 0) */
            /* cmov isn't guaranteed to be available on x86-32 */
            "jnc .1f%=\n"
            "mov $0xFFFFFFFF, %%eax\n"
            ".1f%=:"
            : /* in/out: %eax = result/a, out: edx (ignored) */ "+&a"(a), "=&d"(edx)
            : /* in: operand 2 in reg */ [arg2] "r"(b)
            : /* clobbers: cc */ "cc");
    (void)edx; /* suppress unused warnings */
    return a;
}

/**
 * If a * b overflows, returns AWS_OP_ERR; otherwise multiplies
 * a * b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */
    uint32_t result = a;
    char flag;
    /**
     * Note: We use SETNO which only takes a byte register. To make this easy,
     * we'll write it to dl (which we throw away anyway) and mask off the high bits.
     */
    __asm__("mull %k[arg2]\n" /* eax * b, result is in EDX:EAX, OF=CF=(EDX != 0) */
            "seto %[flag]\n"  /* flag = overflow_bit */
            : /* in/out: %eax (first arg & result), %d (flag) */ "+&a"(result), [flag] "=&d"(flag)
            : /* in: reg for 2nd operand */
            [arg2] "r"(b)
            : /* clobbers: cc (d is used for flag so no need to clobber)*/ "cc");
    *r = result;
    if (flag) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */

    char flag;
    __asm__("addq %[argb], %[arga]\n" /* [arga] = [arga] + [argb] */
            "setc %[flag]\n"          /* [flag] = 1 if overflow, 0 otherwise */
            : /* in/out: */ [arga] "+r"(a), [flag] "=&r"(flag)
            : /* in: */ [argb] "r"(b)
            : /* clobbers: */ "cc");
    *r = a;
    if (flag) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b. If the result overflows, returns 2^64 - 1.
 */
AWS_STATIC_IMPL uint64_t aws_add_u64_saturating(uint64_t a, uint64_t b) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */

    __asm__("addq %[arg1], %[arg2]\n" /* [arga] = [arga] + [argb] */
            "cmovc %q[saturate], %[arg2]\n"
            : /* in/out: %rax = a, out: rdx (ignored) */ [arg2] "+r"(b)
            : /* in: register only */ [arg1] "r"(a),
              /* in: saturation value (reg/memory) */ [saturate] "rm"(~0LL)
            : /* clobbers: cc */ "cc");
    return b;
}

/**
 * If a + b overflows, returns AWS_OP_ERR; otherwise adds
 * a + b, returns the result in *r, and returns AWS_OP_SUCCESS.
 */
AWS_STATIC_IMPL int aws_add_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */

    char flag;
    __asm__("addl %[argb], %[arga]\n" /* [arga] = [arga] + [argb] */
            "setc %[flag]\n"          /* [flag] = 1 if overflow, 0 otherwise */
            : /* in/out: */ [arga] "+r"(a), [flag] "=&r"(flag)
            : /* in: */ [argb] "r"(b)
            : /* clobbers: */ "cc");
    *r = a;
    if (flag) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }
    return AWS_OP_SUCCESS;
}

/**
 * Adds a + b. If the result overflows, returns 2^32 - 1.
 */
AWS_STATIC_IMPL uint32_t aws_add_u32_saturating(uint32_t a, uint32_t b) {
    /* We can use inline assembly to do this efficiently on x86-64 and x86. */

    __asm__("addl %[arg1], %[arg2]\n" /* [arga] = [arga] + [argb] */
            /* cmov isn't guaranteed to be available on x86-32 */
            "jnc .1f%=\n"
            "mov $0xFFFFFFFF, %%eax\n"
            ".1f%=:"
            : /* in/out: %rax = a, out: rdx (ignored) */ [arg2] "+a"(b)
            : /* in: register only */ [arg1] "r"(a)
            : /* clobbers: cc */ "cc");
    return b;
}

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

#endif /* AWS_COMMON_MATH_GCC_X64_ASM_INL */
