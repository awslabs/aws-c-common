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

#undef memset

#include <proof_helpers/nondet.h>
#include <stddef.h>

/**
 * Override the version of memset used by CBMC.
 */
void *memset_impl(void *s, int c, size_t n) {
    __CPROVER_precondition(__CPROVER_w_ok(s, n), "memset destination region writeable");

    return s;
}

void *memset(void *s, int c, size_t n) {
    return memset_impl(s, c, n);
}

void *__builtin___memset_chk(void *s, int c, size_t n, size_t os) {
    (void)os;
    return memset_impl(s, c, n);
}
