/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#undef memmove

#include <proof_helpers/nondet.h>
#include <stdint.h>

/**
 * Override the version of memmove used by CBMC.
 * Source: public domain code copied from https://clc-wiki.net/wiki/memmove
 */
void *memmove_impl(void *dest, const void *src, size_t n) {
    if (n > 0) {
        (void)*(char *)dest;                           /* check that the memory is accessible */
        (void)*(const char *)src;                      /* check that the memory is accessible */
        (void)*(((unsigned char *)dest) + n - 1);      /* check that the memory is accessible */
        (void)*(((const unsigned char *)src) + n - 1); /* check that the memory is accessible */

        unsigned char *pd = dest;
        const unsigned char *ps = src;
        if ((ps) < (pd)) {
            for (pd += n, ps += n; n--;)
                *--pd = *--ps;
        } else {
            while (n) {
                *pd++ = *ps++;
                n--;
            }
        }
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
