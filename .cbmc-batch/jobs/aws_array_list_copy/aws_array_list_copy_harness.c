/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 10s
 */
void aws_array_list_copy_harness() {
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

    __CPROVER_assume(from.item_size == to.item_size);
    __CPROVER_assume(from.data != NULL);

    /* perform operation under verification */
    if (!aws_array_list_copy(&from, &to)) {
        /* In the case aws_array_list_copy is successful, both lists have the same length */
        assert(to.length == from.length);
        assert(to.current_size >= (from.length * from.item_size));
    }

    /* assertions */
    assert(aws_array_list_is_valid(&from));
    assert(aws_array_list_is_valid(&to));
    assert(from.item_size == to.item_size);
}
