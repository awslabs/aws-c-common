/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <proof_helpers/utils.h>
#include <stddef.h>

void *memset_impl(void *dst, int c, size_t n);
void *memset_using_uint64_impl(void *dst, int c, size_t n);

/*
 * Check that the optimized version of memset is memory safe
 * And that it matches the naive version
 */
void memset_using_uint64_harness() {

    short d1[MAX];
    short d2[MAX];
    int c;
    unsigned size;
    __CPROVER_assume(size < MAX);
    memset_impl(d1, c, size);
    memset_using_uint64_impl(d2, c, size);
    assert_bytes_match((uint8_t *)d1, (uint8_t *)d2, size);
    assert_all_bytes_are((uint8_t *)d2, c, size);
}
