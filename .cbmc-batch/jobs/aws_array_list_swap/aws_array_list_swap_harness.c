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
 * Coverage: 0.96 (132 lines out of 138 statically-reachable lines in 19 functions reached)
 * Runtime: 0m7.883s
 *
 * Assumptions:
 *     - a valid aws_array_list structure
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - non-deterministic unsigned int index_a
 *     - non-deterministic unsigned int index_b
 *     - all parameters remain the same after this operation
 */
void aws_array_list_swap_harness() {
    struct aws_array_list *list;
    ASSUME_BOUNDED_ARRAY_LIST(list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);
    struct aws_allocator *alloc = list->alloc;
    size_t current_size = list->current_size;
    size_t length = list->length;
    size_t item_size = list->item_size;
    void *data = list->data;

    size_t index_a = nondet_size_t();
    size_t index_b = nondet_size_t();

    aws_array_list_swap(list, index_a, index_b);

    /* some guarantees */
    assert(list->alloc == alloc);
    assert(list->current_size == current_size);
    assert(list->length == length);
    assert(list->item_size == item_size);
    assert(list->data == data);
}
