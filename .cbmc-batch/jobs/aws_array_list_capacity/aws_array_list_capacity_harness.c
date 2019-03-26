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
 * Coverage: 1.00 (100 lines out of 100 statically-reachable lines in 14 functions reached)
 * Runtime: 0m4.951s
 *
 * Assumptions:
 *     - a valid non-deterministic aws_array_list bounded by initial_item_allocation and item_size
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - non-deterministic length <= initial_item_allocation
 *     - aws_array_list_capacity always returns list->current_size / list->item_size
 *     - all parameters remain the same after this operation
 */
void aws_array_list_capacity_harness() {
    struct aws_array_list *list;
    ASSUME_BOUNDED_ARRAY_LIST(list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);

    struct aws_allocator *alloc = list->alloc;
    size_t current_size = list->current_size;
    size_t length = list->length;
    size_t item_size = list->item_size;
    void *data = list->data;

    size_t capacity = aws_array_list_capacity(list);

    /* assertions */
    assert(capacity == list->current_size / list->item_size);
    assert(list->alloc == alloc);
    assert(list->current_size == current_size);
    assert(list->length == length);
    assert(list->item_size == item_size);
    assert(list->data == data);
}
