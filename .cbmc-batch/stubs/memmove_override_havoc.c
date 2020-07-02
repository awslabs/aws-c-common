/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#undef memmove

#include <proof_helpers/nondet.h>
#include <stdint.h>

/**
 * Override the version of memmove used by CBMC. Users may not want to pay
 * for the cost of performing the computation of memmove in proofs. In that
 * case, this stub at least checks for the preconditions and make sure to
 * havoc all elements pointed by *dest up to n.
 */
void *memmove_impl(void *dest, const void *src, size_t n) {
    __CPROVER_precondition(src != NULL && __CPROVER_r_ok(src, n), "memmove source region readable");
    __CPROVER_precondition(dest != NULL && __CPROVER_w_ok(dest, n), "memmove destination region writeable");

    if (n > 0) {
        size_t index;
        __CPROVER_assume(index < n);
        ((uint8_t *)dest)[index] = nondet_uint8_t();
    }

    return dest;
}

void *memmove(void *dest, const void *src, size_t n) {
    return memmove_impl(dest, src, n);
}

void *__builtin___memmove_chk(void *dest, const void *src, size_t n, size_t size) {
    (void)size;
    return memmove_impl(dest, src, n);
}
