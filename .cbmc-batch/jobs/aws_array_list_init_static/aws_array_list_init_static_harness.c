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

/**
 * Runtime: 7s
 */
void aws_array_list_init_static_harness() {
    /* data structure */
    struct aws_array_list *list;

    /* parameters */
    size_t item_size;
    size_t initial_item_allocation;
    size_t len;

    /* assumptions */
    ASSUME_VALID_MEMORY(list);
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));

    /* perform operation under verification */
    uint8_t *raw_array = bounded_malloc(len);
    aws_array_list_init_static(list, raw_array, initial_item_allocation, item_size);

    /* assertions */
    assert(aws_array_list_is_valid(list));
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->length == 0);
    assert(list->current_size == initial_item_allocation * item_size);
    assert_bytes_match((uint8_t *)list->data, raw_array, len);
}
