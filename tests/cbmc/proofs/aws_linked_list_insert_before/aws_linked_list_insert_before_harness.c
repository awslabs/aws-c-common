/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_insert_before_harness() {
    /* data structure */
    struct aws_linked_list_node before;
    struct aws_linked_list_node before_prev;
    struct aws_linked_list_node to_add;

    before.prev = &before_prev;
    before_prev.next = &before;

    /* perform operation under verification */
    aws_linked_list_insert_before(&before, &to_add);

    /* assertions */
    assert(aws_linked_list_node_prev_is_valid(&before));
    assert(aws_linked_list_node_prev_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&before_prev));

    assert(before.prev == &to_add);
    assert(before_prev.next == &to_add);
}
