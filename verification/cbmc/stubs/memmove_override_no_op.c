/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#undef memmove

#include <proof_helpers/nondet.h>
#include <stdint.h>

/**
 * Override the version of memmove used by CBMC.
 */
void *memmove_impl(void *dest, const void *src, size_t n) {
    if (n > 0) {
        (void)*(char *)dest;                           /* check that the memory is accessible */
        (void)*(const char *)src;                      /* check that the memory is accessible */
        (void)*(((unsigned char *)dest) + n - 1);      /* check that the memory is accessible */
        (void)*(((const unsigned char *)src) + n - 1); /* check that the memory is accessible */
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
