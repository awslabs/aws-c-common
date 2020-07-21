/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_swap_contents_harness() {
    /* data structure */
    struct aws_linked_list a, b;

    ensure_linked_list_is_allocated(&a, MAX_LINKED_LIST_ITEM_ALLOCATION);
    ensure_linked_list_is_allocated(&b, MAX_LINKED_LIST_ITEM_ALLOCATION);

    /* Keep the old first node of the linked lists. Note that we need
     * to save the old head address separately from the list itself
     * because &old_a.head != &a.head (since they are different
     * variables). */
    struct aws_linked_list_node *old_a_head = &a.head;
    struct aws_linked_list old_a = a;
    struct aws_linked_list_node *old_b_head = &b.head;
    struct aws_linked_list old_b = b;

    /* perform operation under verification */
    aws_linked_list_swap_contents(&a, &b);

    /* assertions */
    assert(aws_linked_list_is_valid(&a));
    assert(aws_linked_list_is_valid(&b));

    if (aws_linked_list_empty(&a)) {
        assert(old_b.tail.prev == old_b_head);
    } else {
        assert(a.head.next == old_b.head.next);
        assert(a.tail.prev == old_b.tail.prev);
    }

    if (aws_linked_list_empty(&b)) {
        assert(old_a.tail.prev == old_a_head);
    } else {
        assert(b.head.next == old_a.head.next);
        assert(b.tail.prev == old_a.tail.prev);
    }
}
