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
 */

#undef memcpy

#include <proof_helpers/nondet.h>
#include <stdint.h>

/**
 * Override the version of memcpy used by CBMC.
 */
void *memcpy_impl(void *dst, const void *src, size_t n) {
    __CPROVER_precondition(
        __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
            ((const char *)src >= (const char *)dst + n) || ((const char *)dst >= (const char *)src + n),
        "memcpy src/dst overlap");
    __CPROVER_precondition(__CPROVER_r_ok(src, n), "memcpy source region readable");
    __CPROVER_precondition(__CPROVER_w_ok(dst, n), "memcpy destination region writeable");

    for (__CPROVER_size_t i = 0; i < n; ++i)
        ((char *)dst)[i] = ((const char *)src)[i];

    return dst;
}

void *memcpy(void *dst, const void *src, size_t n) {
    return memcpy_impl(dst, src, n);
}

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
    (void)size;
    return memcpy_impl(dst, src, n);
}
