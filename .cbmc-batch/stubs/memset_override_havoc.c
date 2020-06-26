/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#undef memset

#include <proof_helpers/nondet.h>
#include <stddef.h>

/**
 * Override the version of memset used by CBMC. Users may not want to pay
 * for the cost of performing the computation of memset in proofs. In that
 * case, this stub at least checks for the preconditions and make sure to
 * havoc all elements pointed by *s up to n.
 */
void *memset_impl(void *s, int c, size_t n) {
    __CPROVER_precondition(__CPROVER_w_ok(s, n), "memset destination region writeable");
    if (n > 0) {
        size_t index;
        __CPROVER_assume(index < n);
        ((uint8_t *)s)[index] = nondet_uint8_t();
    }
    return s;
}

void *memset(void *s, int c, size_t n) {
    return memset_impl(s, c, n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os) {
    (void)os;
    return memset_impl(s, c, n);
}
