/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/* FUNCTION: memset */

#ifndef __CPROVER_STRING_H_INCLUDED
#    include <string.h>
#    define __CPROVER_STRING_H_INCLUDED
#endif

#undef memset

void *memset(void *s, int c, size_t n) {
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(s) >= n, "memset buffer overflow");
    if (__CPROVER_is_zero_string(s) && n > __CPROVER_zero_string_length(s)) {
        __CPROVER_is_zero_string(s) = 1;
    } else if (c == 0) {
        __CPROVER_is_zero_string(s) = 1;
        __CPROVER_zero_string_length(s) = 0;
    } else
        __CPROVER_is_zero_string(s) = 0;
#else

    if (n > 0) {
        (void)*(char *)s;             /* check that the memory is accessible */
        (void)*(((char *)s) + n - 1); /* check that the memory is accessible */
        char *sp = s;
        for (__CPROVER_size_t i = 0; i < n; i++)
            sp[i] = c;
    }
#endif
    return s;
}

/* FUNCTION: __builtin_memset */

void *__builtin_memset(void *s, int c, __CPROVER_size_t n) {
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(s) >= n, "memset buffer overflow");
    if (__CPROVER_is_zero_string(s) && n > __CPROVER_zero_string_length(s)) {
        __CPROVER_is_zero_string(s) = 1;
    } else if (c == 0) {
        __CPROVER_is_zero_string(s) = 1;
        __CPROVER_zero_string_length(s) = 0;
    } else {
        __CPROVER_is_zero_string(s) = 0;
    }
#else

    if (n > 0) {
        (void)*(char *)s;             /* check that the memory is accessible */
        (void)*(((char *)s) + n - 1); /* check that the memory is accessible */
        char *sp = s;
        for (__CPROVER_size_t i = 0; i < n; i++)
            sp[i] = c;
    }
#endif
    return s;
}

/* FUNCTION: __builtin___memset_chk */

void *__builtin___memset_chk(void *s, int c, __CPROVER_size_t n, __CPROVER_size_t size) {
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(s) >= n, "memset buffer overflow");
    __CPROVER_precondition(__CPROVER_buffer_size(s) == size, "builtin object size");
    if (__CPROVER_is_zero_string(s) && n > __CPROVER_zero_string_length(s)) {
        __CPROVER_is_zero_string(s) = 1;
    } else if (c == 0) {
        __CPROVER_is_zero_string(s) = 1;
        __CPROVER_zero_string_length(s) = 0;
    } else
        __CPROVER_is_zero_string(s) = 0;
#else
    (void)size;

    if (n > 0) {
        (void)*(char *)s;             /* check that the memory is accessible */
        (void)*(((char *)s) + n - 1); /* check that the memory is accessible */
        char *sp = s;
        for (__CPROVER_size_t i = 0; i < n; i++)
            sp[i] = c;
    }
#endif
    return s;
}
