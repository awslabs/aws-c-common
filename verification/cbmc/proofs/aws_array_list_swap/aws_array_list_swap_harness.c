/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 11s
 */
void aws_array_list_swap_harness() {
    /* data structure */
    struct aws_array_list list;

    /* parameters */
    size_t index_a;
    size_t index_b;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&list);
    __CPROVER_assume(aws_array_list_is_valid(&list));

    __CPROVER_assume(index_a < aws_array_list_length(&list));
    __CPROVER_assume(index_b < aws_array_list_length(&list));

    /* save current state of the data structure */
    struct aws_array_list old = list;

    /* perform operation under verification */
    aws_array_list_swap(&list, index_a, index_b);

    /* assertions */
    assert(aws_array_list_is_valid(&list));
    assert(list.alloc == old.alloc);
    assert(list.current_size == old.current_size);
    assert(list.length == old.length);
    assert(list.item_size == old.item_size);
}
