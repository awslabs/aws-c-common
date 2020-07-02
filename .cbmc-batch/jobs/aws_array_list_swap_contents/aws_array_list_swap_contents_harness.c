/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 7s
 */
void aws_array_list_swap_contents_harness() {
    /* data structure */
    struct aws_array_list from;
    struct aws_array_list to;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&from, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&from);
    __CPROVER_assume(aws_array_list_is_valid(&from));

    __CPROVER_assume(aws_array_list_is_bounded(&to, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&to);
    __CPROVER_assume(aws_array_list_is_valid(&to));

    __CPROVER_assume(from.alloc != NULL);
    __CPROVER_assume(to.alloc != NULL);

    __CPROVER_assume(from.item_size > 0);
    __CPROVER_assume(to.item_size > 0);
    __CPROVER_assume(from.item_size == to.item_size);

    /* save current state of the data structure */
    struct aws_array_list old_from = from;
    struct store_byte_from_buffer old_byte_from;
    save_byte_from_array((uint8_t *)from.data, from.current_size, &old_byte_from);

    struct aws_array_list old_to = to;
    struct store_byte_from_buffer old_byte_to;
    save_byte_from_array((uint8_t *)to.data, to.current_size, &old_byte_to);

    /* perform operation under verification */
    aws_array_list_swap_contents(&from, &to);

    /* assertions */
    assert(aws_array_list_is_valid(&from));
    assert(aws_array_list_is_valid(&to));
    assert_array_list_equivalence(&from, &old_to, &old_byte_to);
    assert_array_list_equivalence(&to, &old_from, &old_byte_from);
}
