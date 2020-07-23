/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: memset
 *
 * Override the version of memset used by CBMC.
 * This takes advantage of the fact that 64bit operations require fewer array updates,
 * which can make this version faster than the naive unrolling when used in CBMC.
 * Benchmark your particular proof to know for sure.
 */

#include <stddef.h>
#include <stdint.h>

void *memset_using_uint64_impl(void *dst, int c, size_t n) {
    __CPROVER_precondition(__CPROVER_w_ok(dst, n), "memset destination region writeable");

    size_t num_uint64s = n >> 3;
    size_t rem = n & 0x7;

    uint8_t *d = (uint8_t *)dst;

    // Use fallthrough to unroll the remainder loop
    switch (rem) {
        case 7:
            d[6] = c;
        case 6:
            d[5] = c;
        case 5:
            d[4] = c;
        case 4:
            d[3] = c;
        case 3:
            d[2] = c;
        case 2:
            d[1] = c;
        case 1:
            d[0] = c;
    }

    d += rem;

    uint64_t compounded = 0;
    if (num_uint64s > 0 && c != 0) {
        uint8_t *chars = (uint8_t *)&compounded;
        chars[0] = c;
        chars[1] = c;
        chars[2] = c;
        chars[3] = c;
        chars[4] = c;
        chars[5] = c;
        chars[6] = c;
        chars[7] = c;
    }

    for (size_t i = 0; i < num_uint64s; ++i) {
        ((uint64_t *)d)[i] = compounded;
    }

    return dst;
}

void *memset(void *s, int c, size_t n) {
    return memset_using_uint64_impl(s, c, n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os) {
    (void)os;
    return memset_using_uint64_impl(s, c, n);
}
