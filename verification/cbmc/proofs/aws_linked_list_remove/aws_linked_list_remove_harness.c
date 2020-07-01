/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_remove_harness() {
    /* data structure */
    struct aws_linked_list_node prev;
    struct aws_linked_list_node next;
    struct aws_linked_list_node node;

    /* Assume the preconditions */
    prev.next = &node;
    node.prev = &prev;
    next.prev = &node;
    node.next = &next;

    /* Note: The function has a precondition that node != NULL */

    /* perform operation under verification */
    aws_linked_list_remove(&node);

    /* assertions */
    assert(aws_linked_list_node_next_is_valid(&prev));
    assert(aws_linked_list_node_prev_is_valid(&next));

    assert(prev.next == &next);
    assert(node.next == NULL);
    assert(node.prev == NULL);
}
