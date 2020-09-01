/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <stddef.h>

/** Abstract memcmp to check that pointers are valid, and then return nondet */

int memcmp(const void *s1, const void *s2, size_t n) {
    //  __CPROVER_HIDE:;
    int res = 0;
    /* `__CPROVER_r_ok` requires a non-zero value for `n`. */
    __CPROVER_precondition(s1 != NULL && (n == 0 || __CPROVER_r_ok(s1, n)), "memcmp region 1 readable");
    __CPROVER_precondition(s2 != NULL && (n == 0 || __CPROVER_r_ok(s2, n)), "memcpy region 2 readable");

#if 1
    const unsigned char *sc1 = s1, *sc2 = s2;
    for (; n != 0; n--) {
        res = (*sc1++) - (*sc2++);
        if (res != 0)
            return res;
    }
    return res;
#else
    return nondet_int();
#endif
}
