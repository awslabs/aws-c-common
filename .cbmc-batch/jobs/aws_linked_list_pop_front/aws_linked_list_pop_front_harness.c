/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_pop_front_harness() {
    /* data structure */
    struct aws_linked_list list;

    ensure_linked_list_is_allocated(&list, MAX_LINKED_LIST_ITEM_ALLOCATION);

    /* Assume the preconditions. The function requires that list != NULL */
    __CPROVER_assume(!aws_linked_list_empty(&list));

    /* Keep the old last node of the linked list */
    struct aws_linked_list_node *old_next_first = (list.head.next)->next;

    /* perform operation under verification */
    struct aws_linked_list_node *ret = aws_linked_list_pop_front(&list);

    /* assertions */
    assert(aws_linked_list_is_valid(&list));
    assert(ret->next == NULL && ret->prev == NULL);
    assert(list.head.next == old_next_first);
}
