/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 2 min
 */
void aws_array_list_push_front_harness() {
    /* Data structure. */
    struct aws_array_list list;

    /*
     * We need to bound the input to cope with the complexity of checking arithmetic operations
     * (i.e., multiplications) over item_size and length. This is a limitation of CBMC.
     */
    __CPROVER_assume(aws_array_list_is_bounded(&list, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));

    /* Non-deterministic allocations. */
    ensure_array_list_has_allocated_data_member(&list);
    void *val = malloc(list.item_size);

    /* Save current state of the data structure. */
    struct aws_array_list old = list;
    struct store_byte_from_buffer old_byte;
    if (list.data != NULL) {
        save_byte_from_array((uint8_t *)list.data, list.current_size, &old_byte);
    }

    /* Assume preconditions. */
    __CPROVER_assume(aws_array_list_is_valid(&list));
    __CPROVER_assume(val && AWS_MEM_IS_READABLE(val, list.item_size));

    /* Perform operation under verification and check postconditions. */
    if (aws_array_list_push_front(&list, val) == AWS_OP_SUCCESS) {
        assert(list.length == old.length + 1);
    } else if (list.data != NULL) {
        /* In the case aws_array_list_push_front is not successful, the list must not change. */
        assert_array_list_equivalence(&list, &old, &old_byte);
    }
    assert(aws_array_list_is_valid(&list));
}
