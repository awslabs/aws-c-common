/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_next_harness() {
    /* data structure */
    struct aws_linked_list_node node;  // Preconditions require node to not be NULL
    struct aws_linked_list_node after; // Preconditions require after to not be NULL

    /* Assume the preconditions */
    node.next = &after;
    after.prev = &node;

    /* perform operation under verification */
    struct aws_linked_list_node *rval = aws_linked_list_next(&node);

    /* assertions */
    assert(aws_linked_list_node_next_is_valid(&node));
    assert(aws_linked_list_node_prev_is_valid(rval));
    assert(rval == &after);
}
