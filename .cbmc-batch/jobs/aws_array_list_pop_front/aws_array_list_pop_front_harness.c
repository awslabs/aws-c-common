/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 9s
 */
void aws_array_list_pop_front_harness() {
    /* data structure */
    struct aws_array_list list;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&list);
    __CPROVER_assume(aws_array_list_is_valid(&list));

    /* save current state of the data structure */
    struct aws_array_list old = list;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array((uint8_t *)list.data, list.current_size, &old_byte);

    /* perform operation under verification and assertions */
    if (!aws_array_list_pop_front(&list)) {
        assert(list.length == old.length - 1);
        assert(list.data);
        assert(list.alloc == old.alloc);
        assert(list.current_size == old.current_size);
        assert(list.item_size == old.item_size);
    } else {
        /* In the case aws_array_list_pop_front is not successful, the list must not change */
        assert_array_list_equivalence(&list, &old, &old_byte);
    }
    assert(aws_array_list_is_valid(&list));
}
