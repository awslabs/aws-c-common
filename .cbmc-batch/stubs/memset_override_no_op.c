/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#undef memset

#include <proof_helpers/nondet.h>
#include <stddef.h>

/**
 * Override the version of memset used by CBMC.
 */
void *memset_impl(void *s, int c, size_t n) {
    __CPROVER_precondition(__CPROVER_w_ok(s, n), "memset destination region writeable");

    return s;
}

void *memset(void *s, int c, size_t n) {
    return memset_impl(s, c, n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os) {
    (void)os;
    return memset_impl(s, c, n);
}
