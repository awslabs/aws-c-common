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

/* FUNCTION: memmove */

#ifndef __CPROVER_STRING_H_INCLUDED
#    include <string.h>
#    define __CPROVER_STRING_H_INCLUDED
#endif

#undef memmove

void *memmove(void *dest, const void *src, size_t n) {
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(src) >= n, "memmove buffer overflow");
    /* dst = src (with overlap allowed) */
    if (__CPROVER_is_zero_string(src) && n > __CPROVER_zero_string_length(src)) {
        __CPROVER_is_zero_string(src) = 1;
        __CPROVER_zero_string_length(dest) = __CPROVER_zero_string_length(src);
    } else
        __CPROVER_is_zero_string(dest) = 0;
#else

    if (n > 0) {
        (void)*(char *)dest;                  /* check that the memory is accessible */
        (void)*(const char *)src;             /* check that the memory is accessible */
        (void)*(((char *)dest) + n - 1);      /* check that the memory is accessible */
        (void)*(((const char *)src) + n - 1); /* check that the memory is accessible */
        char src_n[n];
        __CPROVER_array_copy(src_n, (char *)src);
        __CPROVER_array_replace((char *)dest, src_n);
    }
#endif
    return dest;
}

/* FUNCTION: __builtin___memmove_chk */

#ifndef __CPROVER_STRING_H_INCLUDED
#    include <string.h>
#    define __CPROVER_STRING_H_INCLUDED
#endif

#undef memmove

/**
 * Source: https://clc-wiki.net/wiki/memmove
 */
void *impl_memmove(void *dest, const void *src, size_t n) {
    unsigned char *pd = dest;
    const unsigned char *ps = src;
    if ((ps) < (pd))
        for (pd += n, ps += n; n--;)
            *--pd = *--ps;
    else if (!n)
        while (n--)
            *pd++ = *ps++;
    return dest;
}

void *__builtin___memmove_chk(void *dest, const void *src, size_t n, __CPROVER_size_t size) {
__CPROVER_HIDE:;
#ifdef __CPROVER_STRING_ABSTRACTION
    __CPROVER_precondition(__CPROVER_buffer_size(src) >= n, "memmove buffer overflow");
    __CPROVER_precondition(__CPROVER_buffer_size(dest) == size, "builtin object size");
    /* dst = src (with overlap allowed) */
    if (__CPROVER_is_zero_string(src) && n > __CPROVER_zero_string_length(src)) {
        __CPROVER_is_zero_string(src) = 1;
        __CPROVER_zero_string_length(dest) = __CPROVER_zero_string_length(src);
    } else {
        __CPROVER_is_zero_string(dest) = 0;
    }
#else
    (void)size;

    if (n > 0) {
        (void)*(char *)dest;                  /* check that the memory is accessible */
        (void)*(const char *)src;             /* check that the memory is accessible */
        (void)*(((char *)dest) + n - 1);      /* check that the memory is accessible */
        (void)*(((const char *)src) + n - 1); /* check that the memory is accessible */
        impl_memmove(dest, src, n);
        // char src_n[n];
        //__CPROVER_array_copy(src_n, (char *)src);
        //__CPROVER_array_replace((char *)dest, src_n);
    }
#endif
    return dest;
}
