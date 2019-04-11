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

#pragma once
#include <aws/common/common.h>

/*
 * CBMC has an internal representation in which each object has an index and an offset
 * A buffer cannot be larger than the max size of the offset
 * The Makefile is expected to set CBMC_OBJECT_BITS to the value of --object-bits
 */
#define MAX_MALLOC (SIZE_MAX >> (CBMC_OBJECT_BITS + 1))

/**
 * The standard allocator in CBMC cannot fail.
 * This one can, which allows us to
 * nondeterministically find more bugs
 */
struct aws_allocator *can_fail_allocator();

static void *can_fail_malloc_allocator(struct aws_allocator *allocator, size_t size);

void *can_fail_malloc(size_t size);

/**
 * CBMC considers malloc always successed for any given size. However, a real machine
 * can only provide the available size from the pointer until the end of the address space.
 * This function models the real machine behaviour.
 */
void *bounded_malloc(size_t size);

static void can_fail_free(struct aws_allocator *allocator, void *ptr);

static void *can_fail_realloc(struct aws_allocator *allocator, void *ptr, size_t oldsize, size_t newsize);

static struct aws_allocator can_fail_allocator_static = {
    .mem_acquire = can_fail_malloc_allocator,
    .mem_release = can_fail_free,
    .mem_realloc = can_fail_realloc,
};
