/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
 * This function overrides the original implementation of the memcpy function
 * from string.h. It copies the values of n bytes from the *src to the *dst.
 * It also checks if the size of the arrays pointed to by both the *dst and
 * *src parameters are at least n bytes and if they overlap.
 */

#ifndef __CPROVER_STRING_H_INCLUDED
#    include <string.h>
#    define __CPROVER_STRING_H_INCLUDED
#endif

#undef memcpy

void *memcpy(void *dst, const void *src, size_t n) {
__CPROVER_HIDE:
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(src) >= n, "memcpy buffer overflow");
    __CPROVER_precondition(__CPROVER_buffer_size(dst) >= n, "memcpy buffer overflow");
    if (__CPROVER_is_zero_string(src) && n > __CPROVER_zero_string_length(src)) {
        __CPROVER_is_zero_string(dst) = 1;
        __CPROVER_zero_string_length(dst) = __CPROVER_zero_string_length(src);
    } else if (!(__CPROVER_is_zero_string(dst) && n <= __CPROVER_zero_string_length(dst)))
        __CPROVER_is_zero_string(dst) = 0;
#else
    __CPROVER_precondition(__CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src), "memcpy src/dst overlap");

    if (n > 0) {
        (void)*(char *)dst;                   /* check that the memory is accessible */
        (void)*(const char *)src;             /* check that the memory is accessible */
        (void)*(((char *)dst) + n - 1);       /* check that the memory is accessible */
        (void)*(((const char *)src) + n - 1); /* check that the memory is accessible */
        for (__CPROVER_size_t i = 0; i < n; i++)
            ((char *)dst)[i] = ((const char *)src)[i];
    }
#endif
    return dst;
}

/* FUNCTION: __builtin___memcpy_chk */

void *__builtin___memcpy_chk(void *dst, const void *src, __CPROVER_size_t n, __CPROVER_size_t size) {
__CPROVER_HIDE:
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(src) >= n, "memcpy buffer overflow");
    __CPROVER_precondition(__CPROVER_buffer_size(dst) >= n, "memcpy buffer overflow");
    __CPROVER_precondition(__CPROVER_buffer_size(dst) == s, "builtin object size");
    if (__CPROVER_is_zero_string(src) && n > __CPROVER_zero_string_length(src)) {
        __CPROVER_is_zero_string(dst) = 1;
        __CPROVER_zero_string_length(dst) = __CPROVER_zero_string_length(src);
    } else if (!(__CPROVER_is_zero_string(dst) && n <= __CPROVER_zero_string_length(dst)))
        __CPROVER_is_zero_string(dst) = 0;
#else
    __CPROVER_precondition(__CPROVER_POINTER_OBJECT(dst) != __CPROVER_POINTER_OBJECT(src), "memcpy src/dst overlap");
    (void)size;

    if (n > 0) {
        (void)*(char *)dst;                   /* check that the memory is accessible */
        (void)*(const char *)src;             /* check that the memory is accessible */
        (void)*(((char *)dst) + n - 1);       /* check that the memory is accessible */
        (void)*(((const char *)src) + n - 1); /* check that the memory is accessible */
        for (__CPROVER_size_t i = 0; i < n; i++)
            ((char *)dst)[i] = ((const char *)src)[i];
    }
#endif
    return dst;
}
