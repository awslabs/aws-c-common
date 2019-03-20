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

#include <proof_helpers/proof_allocators.h>
#include <stdlib.h>

/**
 * Use the same functions as the standard default allocator, but nondeterministically
 * have malloc return null.  This is needed because the CBMC model of malloc cannot
 * fail, so we cannot test the null case otherwise.
 */
static void *can_fail_malloc_allocator(struct aws_allocator *allocator, size_t size) {
    (void)allocator;
    if (size > MAX_MALLOC)
        return NULL;
    int nondet;
    return (nondet) ? NULL : malloc(size);
}

void *can_fail_malloc(size_t size) {
    if (size > MAX_MALLOC)
        return NULL;
    int nondet;
    return (nondet) ? NULL : malloc(size);
}

static void can_fail_free(struct aws_allocator *allocator, void *ptr) {
    (void)allocator;
    free(ptr);
}

static void *can_fail_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize) {
    (void)allocator;
    (void)oldsize;
    if (newsize > MAX_MALLOC)
        return NULL;
    int nondet;
    return (nondet) ? NULL : realloc(ptr, newsize);
}

struct aws_allocator *can_fail_allocator() {
    return &can_fail_allocator_static;
}
