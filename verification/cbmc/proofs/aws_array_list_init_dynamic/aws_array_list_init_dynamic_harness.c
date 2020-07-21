/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 6s
 */
void aws_array_list_init_dynamic_harness() {
    /* data structure */
    struct aws_array_list list; /* Precondition: list is non-null */

    /* parameters */
    struct aws_allocator *allocator = can_fail_allocator(); /* Precondition: allocator is non-null */
    size_t item_size;
    size_t initial_item_allocation;

    /* assumptions */
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    __CPROVER_assume(item_size > 0 && item_size <= MAX_ITEM_SIZE);

    /* perform operation under verification */
    if (aws_array_list_init_dynamic(&list, allocator, initial_item_allocation, item_size) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_array_list_is_valid(&list));
        assert(list.alloc == allocator);
        assert(list.item_size == item_size);
        assert(list.length == 0);
        assert(list.current_size == item_size * initial_item_allocation);
    } else {
        /*assertions */
        assert(AWS_IS_ZEROED(list));
    }
}
