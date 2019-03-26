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

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

#define MAX_ITEM_SIZE 2
#define MAX_INITIAL_ITEM_ALLOCATION (UINT64_MAX / MAX_ITEM_SIZE) + 1

/**
 * Coverage: 1.00 (121 lines out of 121 statically-reachable lines in 14 functions reached)
 * Runtime: 0m6.435s
 *
 * Assumptions:
 *     - two valid non-deterministic aws_array_list bounded by initial_item_allocation and item_size
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - non-deterministic length <= initial_item_allocation for both aws_array_list
 *     - from->alloc != NULL
 *     - from->alloc == to->alloc
 *     - from->item_size == to->item_size
 *     - after this operation, from == previous to
 *     - after this operation, to == previous from
 */
void aws_array_list_swap_contents_harness() {
    struct aws_array_list *from;
    ASSUME_BOUNDED_ARRAY_LIST(from, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);
    struct aws_allocator *from_alloc = from->alloc;
    size_t from_current_size = from->current_size;
    size_t from_length = from->length;
    size_t from_item_size = from->item_size;
    void *from_data = from->data;

    struct aws_array_list *to;
    ASSUME_BOUNDED_ARRAY_LIST(to, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);
    struct aws_allocator *to_alloc = to->alloc;
    size_t to_current_size = to->current_size;
    size_t to_length = to->length;
    size_t to_item_size = to->item_size;
    void *to_data = to->data;

    __CPROVER_assume(from->alloc);
    __CPROVER_assume(from->alloc == to->alloc);
    __CPROVER_assume(from->item_size == to->item_size);

    aws_array_list_swap_contents(from, to);

    /* some guarantees */
    assert(from->item_size == to_item_size);
    assert(from->length == to_length);
    assert(from->alloc == to_alloc);
    assert(from->current_size == to_current_size);
    assert(from->item_size == to_item_size);
    assert(from->data == to_data);
    assert(to->item_size == from_item_size);
    assert(to->length == from_length);
    assert(to->alloc == from_alloc);
    assert(to->current_size == from_current_size);
    assert(to->item_size == from_item_size);
    assert(to->data == from_data);
}
