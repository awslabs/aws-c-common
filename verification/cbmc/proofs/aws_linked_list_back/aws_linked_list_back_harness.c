/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_back_harness() {
    /* data structure */
    struct aws_linked_list list;

    ensure_linked_list_is_allocated(&list, MAX_LINKED_LIST_ITEM_ALLOCATION);

    /* Keep the old last node of the linked list */
    struct aws_linked_list_node *old_last = list.tail.prev;

    /* Assume the preconditions. The function requires that list != NULL */
    __CPROVER_assume(!aws_linked_list_empty(&list));

    /* perform operation under verification */
    struct aws_linked_list_node *back = aws_linked_list_back(&list);

    /* assertions */
    assert(aws_linked_list_is_valid(&list));
    assert(aws_linked_list_node_prev_is_valid(back));
    assert(aws_linked_list_node_next_is_valid(back));
    assert(back == old_last);
}
