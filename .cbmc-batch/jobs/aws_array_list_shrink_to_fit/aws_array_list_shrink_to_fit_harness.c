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
 * Runtime: 0m51.653s
 *
 * Assumptions:
 *     - a valid aws_array_list structure
 *     - non-deterministic initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION
 *     - non-deterministic item_size <= MAX_ITEM_SIZE
 *     - aws_array_list_shrink_to_fit == AWS_OP_SUCCESS
 *                                 -> (list->length == 0 && list->data == NULL) ||
 *                                    (list->data != NULL &&
 *                                     list->current_size == list->length * list->item_size)
 */
void aws_array_list_shrink_to_fit_harness() {
    struct aws_array_list *list;
    ASSUME_BOUNDED_ARRAY_LIST(list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE);
    size_t n = nondet_size_t();
    aws_array_list_pop_front_n(list, n);
    if (!aws_array_list_shrink_to_fit(list)) {
        assert(
            (list->length == 0 && list->data == NULL) ||
            (list->data != NULL && list->current_size == list->length * list->item_size));
    }
}
