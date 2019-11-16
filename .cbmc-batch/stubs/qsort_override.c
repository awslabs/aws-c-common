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
