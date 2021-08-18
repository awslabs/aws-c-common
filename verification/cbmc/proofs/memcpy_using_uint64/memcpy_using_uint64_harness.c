/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <proof_helpers/utils.h>
#include <stddef.h>

void *memcpy_impl(void *dst, const void *src, size_t n);
void *memcpy_using_uint64_impl(void *dst, const void *src, size_t n);

/*
 * Check that the optimized version of memcpy is memory safe
 * And that it matches the naive version
 */
void memcpy_using_uint64_harness() {
    char s[MAX];
    char d1[MAX];
    char d2[MAX];

    unsigned size;
    __CPROVER_assume(size < MAX);
    memcpy_impl(d1, s, size);
    memcpy_using_uint64_impl(d2, s, size);
    assert_bytes_match(d1, d2, size);
}
