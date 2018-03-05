#ifndef AWS_COMMON_math_H
#define AWS_COMMON_math_H

#include <stdint.h>
#include <stdlib.h>

#if defined(_M_X64) || defined(_M_IX86) || defined(_M_ARM)
#include <intrin.h>
#include <immintrin.h>
#endif

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

/**
 * Multiplies a * b. If the result overflows, returns 2^64 - 1.
 */
static inline uint64_t aws_common_mul_u64_saturating(uint64_t a, uint64_t b) {
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
    // We can use inline assembly to do this efficiently on x86-64 and x86.

    // we specify rdx as an output, rather than a clobber, because we want to
    // allow it to be allocated as an input register

    uint64_t rdx;
    __asm__ (
        "mulq %q2\n" // rax * b, result is in RDX:RAX, OF=CF=(RDX != 0)
        "cmovc %q3, %%rax\n"
        : /* in/out: %rax = a, out: rdx (ignored) */ "+a" (a), "=d" (rdx)
        : /* in: register */ "r" (b),
          /* in: saturation value (reg/memory) */ "rm" (~0LL)
        : /* clobbers: cc */ "cc"
    );
    (void)rdx; // suppress unused warnings
    return a;
#elif defined(_M_X64) || defined(_M_ARM)
    uint64_t out;
    uint64_t ret_val = _umul128(a, b, &out);
    return out == 0 ? ret_val : ~(uint64_t)0;
#else
    uint64_t x = a * b;
    if (a != 0 && (a > 0xFFFFFFFF || b > 0xFFFFFFFF) && x / a != b) {
        return ~(uint64_t)0;
    } else {
        return x;
    }
#endif
}

/**
 * Multiplies a * b and returns the truncated result in *r. If the result
 * overflows, returns 0, else returns 1.
 */
static inline int aws_common_mul_u64_checked(uint64_t a, uint64_t b, uint64_t *r) {
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
    // We can use inline assembly to do this efficiently on x86-64 and x86.

    int flag;
    uint64_t result;
    __asm__(
        "mulq %3\n" // rax * b, result is in RDX:RAX, OF=CF=(RDX != 0)
        "setno %b1\n" // rdx = (OF = 0)
        "and $0xFF, %1\n" // mask out flag
        : /* out: %rax */ "=a" (result), "=d" (flag)
        : /* in: reg or memory (possibly rax/rdx), reg for 2nd operand */
          "a" (a), "r" (b)
        : /* clobbers: cc */ "cc"
    );
    *r = result;
    return flag;
#elif defined(_M_X64) || defined(_M_ARM)
    uint64_t out;
    *r = _umul128(a, b, &out);

    return out == 0;
#else
    uint64_t x = a * b;
    *r = x;
    if (a != 0 && (a > 0xFFFFFFFF || b > 0xFFFFFFFF) && x / a != b) {
        return 0;
    } else {
        return 1;
    }
#endif
}

/**
 * Multiplies a * b. If the result overflows, returns 2^32 - 1.
 */
static inline uint32_t aws_common_mul_u32_saturating(uint32_t a, uint32_t b) {
#if (defined(__i386__) || defined(__x86_64__)) && (defined(__GNUC__) || defined(__clang__))
    // We can use inline assembly to do this efficiently on x86-64 and x86.

    // we specify edx as an output, rather than a clobber, because we want to allow it
    // to be allocated as an input register
    uint32_t edx;
    __asm__(
        "mull %k3\n" // eax * b, result is in EDX:EAX, OF=CF=(EDX != 0)
#ifdef __x86_64__
        "cmovc %k4, %%eax\n"
#else
        // cmov isn't guaranteed to be available on x86-32
        "jno .1f\n"
        "mov $0xFFFFFFFF, %%eax\n"
        ".1f:"
#endif
        : /* out: %rax = result/a, out: rdx (ignored) */ "=a" (a), "=d" (edx)
        : /* in: operand 1 in eax */ "a" (a),
          /* in: operand 2 in reg */ "r" (b)
#ifdef __x86_64__
        // Saturation value for CMOV to use
            , "r" (0xFFFFFFFF)
#endif
        : /* clobbers: cc */ "cc"
    );
    (void)edx; // suppress unused warnings
    return a;
#elif defined(_M_X64) || defined(_M_IX86)
    uint32_t out;
    uint32_t ret_val = _mulx_u32(a, b, &out);
    return out == 0 ? ret_val : ~(uint32_t)0;
#else
    uint32_t x = a * b;
    if (a != 0 && (a > 0xFFFF || b > 0xFFFF) && x / a != b) {
        return ~(uint32_t)0;
    } else {
        return x;
    }
#endif
}

/**
 * Multiplies a * b and returns the result in *r. If the result overflows,
 * returns 0, else returns 1.
 */
static inline int aws_common_mul_u32_checked(uint32_t a, uint32_t b, uint32_t *r) {
#if (defined(__i386__) || defined(__x86_64__)) && (defined(__GNUC__) || defined(__clang__))
    // We can use inline assembly to do this efficiently on x86-64 and x86.
    uint32_t result;
    int flag;
    // Note: We use SETNO which only takes a byte register. To make this easy,
    // we'll write it to dl (which we throw away anyway) and mask off the high
    // bits.
    __asm__(
        "mull %k3\n" // eax * b, result is in EDX:EAX, OF=CF=(EDX != 0)
        "setno %%dl\n" // flag = !OF ^ (junk in top 24 bits)
        "and $0xFF, %%edx\n" // flag = flag & 0xFF
        // we allocate flag to EDX since it'll be clobbered by MUL anyway
        : /* in/out: %eax = a, %dl = flag */ "=a" (result), "=d" (flag)
        : /* in: eax = a, anything reg = b */ "a" (a), "r" (b)
        : /* clobbers: cc */ "cc"
    );
    *r = result;
    return flag;
#elif defined(_M_X64) || defined(_M_IX86)
    uint32_t out;
    *r = _mulx_u32(a, b, &out);

    return out == 0;
#else
    uint32_t x = a * b;
    *r = x;
    if (a != 0 && (a > 0xFFFF || b > 0xFFFF) && x / a != b) {
        return 0;
    } else {
        return 1;
    }
#endif
}

#if _MSC_VER
#pragma warning(push)
#pragma warning(disable:4127) /*Disable "conditional expression is constant" */
#endif /* _MSC_VER */

static inline size_t aws_common_mul_size_saturating(size_t a, size_t b) {
    /* static assert: SIZE_MAX == (~(uint32_t)0) || (~(uint64_t)0)*/
    char assert_sizet_is_32_or_64_bit[
        (((uint64_t)SIZE_MAX == (uint64_t)~(uint32_t)0) ||
        ((uint64_t)SIZE_MAX == (uint64_t)~(uint64_t)0))
        ? 1 : -1
    ];
    /* suppress unused variable warning */
    (void)assert_sizet_is_32_or_64_bit;



    if ((uint64_t)SIZE_MAX == (uint64_t)~(uint32_t)0) {
        return (size_t)aws_common_mul_u32_saturating((uint32_t)a, (uint32_t)b);
    } else {
        return (size_t)aws_common_mul_u64_saturating(a, b);
    }
}

static inline int aws_common_mul_size_checked(size_t a, size_t b, size_t *r) {
    if ((uint64_t)SIZE_MAX == (uint64_t)~(uint32_t)0) {
        return (int)aws_common_mul_u32_checked((uint32_t)a, (uint32_t)b, (uint32_t*)r);
    } else {
        return (int)aws_common_mul_u64_checked((uint32_t)a, (uint32_t)b, (uint64_t*)r);
    }
}

#if _MSC_VER
#pragma warning(pop)
#endif /* _MSC_VER */

#endif
