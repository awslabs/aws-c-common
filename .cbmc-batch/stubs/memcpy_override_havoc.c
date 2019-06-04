/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * FUNCTION: memcpy
 *
 * This function overrides the original implementation of the memcpy
 * function from string.h. It just assignes a non deterministic value
 * to a non deterministic index [i] <= [n] of the destination array It
 * also checks if the size of the arrays pointed to by both the [*dst]
 * and [*src] parameters are at least [n] bytes and if they overlap.
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
