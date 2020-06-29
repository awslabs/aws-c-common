/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <stdint.h>

void qsort(void *base, __CPROVER_size_t num, __CPROVER_size_t size, int (*compare)(const void *, const void *)) {
    __CPROVER_precondition(__CPROVER_r_ok(base, num * size), "qsort base region readable");
    __CPROVER_precondition(__CPROVER_w_ok(base, num * size), "qsort base region writeable");
    __CPROVER_size_t index_a;
    __CPROVER_assume(index_a < num);
    __CPROVER_size_t index_b;
    __CPROVER_assume(index_b < num);
    __CPROVER_assume(index_a != index_b);
    compare((uint8_t *)base + (size * index_a), (uint8_t *)base + (size * index_b));
}
