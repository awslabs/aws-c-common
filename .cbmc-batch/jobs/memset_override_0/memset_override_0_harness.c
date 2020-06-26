/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <proof_helpers/utils.h>
#include <stddef.h>

void *memset_impl(void *dst, int c, size_t n);
void *memset_override_0_impl(void *dst, int c, size_t n);

/*
 * Check that the optimized version of memset is memory safe
 * And that it matches the naive version
 */
void memset_override_0_harness() {

    short d1[MAX];
    short d2[MAX];
    int c;
    __CPROVER_assume(c == 0); // asserted in the implementation

    unsigned size;
    __CPROVER_assume((size & 0x7) == 0); // asserted in the implementation
    __CPROVER_assume(size < MAX);
    memset_impl(d1, c, size);
    memset_override_0_impl(d2, c, size);
    assert_bytes_match((uint8_t *)d1, (uint8_t *)d2, size);
    assert_all_bytes_are((uint8_t *)d2, c, size);
}
