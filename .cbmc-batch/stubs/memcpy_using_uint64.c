/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: memcpy
 *
 * This function overrides the original implementation of the memcpy function
 * from string.h. It copies the values of n bytes from the *src to the *dst.
 * It also checks if the size of the arrays pointed to by both the *dst and
 * *src parameters are at least n bytes and if they overlap.
 *
 * This takes advantage of the fact that 64bit operations require fewer array updates,
 * which can make this version faster than the naive unrolling when used in CBMC.
 * Benchmark your particular proof to know for sure.
 */

#include <stddef.h>
#include <stdint.h>

void *memcpy_using_uint64_impl(void *dst, const void *src, size_t n) {
    __CPROVER_precondition(
        __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
            ((const char *)src >= (const char *)dst + n) || ((const char *)dst >= (const char *)src + n),
        "memcpy src/dst overlap");
    __CPROVER_precondition(__CPROVER_r_ok(src, n), "memcpy source region readable");
    __CPROVER_precondition(__CPROVER_w_ok(dst, n), "memcpy destination region writeable");

    size_t num_uint64s = n >> 3;
    size_t rem = n & 0x7;

    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;

    // Use fallthrough to unroll the remainder loop
    switch (rem) {
        case 7:
            d[6] = s[6];
        case 6:
            d[5] = s[5];
        case 5:
            d[4] = s[4];
        case 4:
            d[3] = s[3];
        case 3:
            d[2] = s[2];
        case 2:
            d[1] = s[1];
        case 1:
            d[0] = s[0];
    }

    d += rem;
    s += rem;

    for (size_t i = 0; i < num_uint64s; ++i) {
        ((uint64_t *)d)[i] = ((const uint64_t *)s)[i];
    }

    return dst;
}

void *memcpy(void *dst, const void *src, size_t n) {
    return memcpy_using_uint64_impl(dst, src, n);
}

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
    (void)size;
    return memcpy_using_uint64_impl(dst, src, n);
}
