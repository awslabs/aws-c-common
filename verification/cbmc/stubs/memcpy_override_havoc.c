/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#undef memcpy

#include <proof_helpers/nondet.h>
#include <stdint.h>

/**
 * Override the version of memcpy used by CBMC. Users may not want to pay
 * for the cost of performing the computation of memcpy in proofs. In that
 * case, this stub at least checks for the preconditions and make sure to
 * havoc all elements pointed by *dst up to n.
 */
void *memcpy_impl(void *dst, const void *src, size_t n) {
    __CPROVER_precondition(
        __CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src) ||
            ((const char *)src >= (const char *)dst + n) || ((const char *)dst >= (const char *)src + n),
        "memcpy src/dst overlap");
    __CPROVER_precondition(src != NULL && __CPROVER_r_ok(src, n), "memcpy source region readable");
    __CPROVER_precondition(dst != NULL && __CPROVER_w_ok(dst, n), "memcpy destination region writeable");

    if (n > 0) {
        size_t index;
        __CPROVER_assume(index < n);
        ((uint8_t *)dst)[index] = nondet_uint8_t();
    }
    return dst;
}

void *memcpy(void *dst, const void *src, size_t n) {
    return memcpy_impl(dst, src, n);
}

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
    (void)size;
    return memcpy_impl(dst, src, n);
}
