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
 * Coverage: 1.00 (58 lines out of 58 statically-reachable lines in 9 functions reached)
 * Runtime: 0m3.955s
 *
 * Assumptions:
 *     - a valid aws_array_list structure
 *     - a valid aws_allocator structure
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - aws_array_list_init_dynamic == AWS_OP_SUCCESS
 *                                 -> list->alloc == allocator
 *                                 -> list->item_size == item_size
 *                                 -> list->length == 0
 *                                 -> list->data == NULL && list->current_size == 0
 *                                    || list->data &&
 *                                       list->current_size == initial_item_allocation * item_size
 */
void aws_array_list_init_dynamic_harness() {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    struct aws_allocator *allocator;
    ASSUME_CAN_FAIL_ALLOCATOR(allocator);
    size_t initial_item_allocation = nondet_size_t();
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);

    /* some guarantees */
    if (!aws_array_list_init_dynamic(list, allocator, initial_item_allocation, item_size)) {
        assert(list->alloc == allocator);
        assert(list->item_size == item_size);
        assert(list->length == 0);
        assert(
            (list->data == NULL && list->current_size == 0) ||
            (list->data && list->current_size == (initial_item_allocation * item_size)));
    }
}
