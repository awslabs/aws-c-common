/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <stddef.h>

/** Abstract memcmp to check that pointers are valid, and then return nondet */

int memcmp(const void *s1, const void *s2, size_t n) {
    __CPROVER_precondition(__CPROVER_r_ok(s1, n), "memcmp region 1 readable");
    __CPROVER_precondition(__CPROVER_r_ok(s2, n), "memcpy region 2 readable");

    return nondet_int();
}
