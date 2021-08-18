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

void *memset_override_0_impl(void *dst, int c, size_t n) {
    __CPROVER_precondition(__CPROVER_w_ok(dst, n), "memset destination region writeable");

    assert(c == 0);
    size_t num_uint64s = n >> 3;
    size_t rem = n & 0x7;
    assert(rem == 0);

    uint64_t *d = (uint64_t *)dst;

    for (size_t i = 0; i < num_uint64s; ++i) {
        d[i] = 0;
    }

    return dst;
}

void *memset(void *s, int c, size_t n) {
    return memset_override_0_impl(s, c, n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os) {
    (void)os;
    return memset_override_0_impl(s, c, n);
}
