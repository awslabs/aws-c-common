/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 4 min
 */
void aws_array_list_push_back_harness() {
    /* data structure */
    struct aws_array_list list;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&list);
    __CPROVER_assume(aws_array_list_is_valid(&list));
    __CPROVER_assume(list.data != NULL);
    void *val = malloc(list.item_size);

    /* save current state of the data structure */
    struct aws_array_list old = list;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array((uint8_t *)list.data, list.current_size, &old_byte);

    /* assume preconditions */
    __CPROVER_assume(aws_array_list_is_valid(&list));
    __CPROVER_assume(val && AWS_MEM_IS_READABLE(val, list.item_size));

    /* perform operation under verification and assertions */
    if (!aws_array_list_push_back(&list, val)) {
        assert(list.length == old.length + 1);
    } else {
        /* In the case aws_array_list_push_back is not successful, the list must not change */
        assert_array_list_equivalence(&list, &old, &old_byte);
    }
    assert(aws_array_list_is_valid(&list));
}
