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
 * Coverage: 1.00 (38 lines out of 38 statically-reachable lines in 6 functions reached)
 * Runtime: 0m3.378s
 *
 * Assumptions:
 *     - a valid aws_array_list structure
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - void* raw_arry of length == initial_item_allocation * item_size
 *     - aws_array_list_init_static == AWS_OP_SUCCESS
 *                                 -> list->alloc == NULL
 *                                 -> list->item_size == item_size
 *                                 -> list->data == raw_array
 *                                 -> list->length == 0
 *                                 -> list->current_size == initial_item_allocation * item_size
 */
void aws_array_list_init_static_harness() {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    size_t initial_item_allocation = nondet_size_t();
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    size_t len;
    __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));
    void *raw_array = malloc(len);

    aws_array_list_init_static(list, raw_array, initial_item_allocation, item_size);

    /* assertions */
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->data == raw_array);
    assert(list->length == 0);
    assert(list->current_size == initial_item_allocation * item_size);
}
