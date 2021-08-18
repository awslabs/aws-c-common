/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_push_front_harness() {
    /* data structure */
    struct aws_linked_list list;
    struct aws_linked_list_node to_add;

    ensure_linked_list_is_allocated(&list, MAX_LINKED_LIST_ITEM_ALLOCATION);

    struct aws_linked_list_node *old_first = list.head.next;
    /* perform operation under verification */
    aws_linked_list_push_front(&list, &to_add);

    /* assertions */
    assert(aws_linked_list_is_valid(&list));
    assert(aws_linked_list_node_prev_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&to_add));
    assert(list.head.next == &to_add);
    assert(to_add.next == old_first);
}
