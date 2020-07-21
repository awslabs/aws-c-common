/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_insert_after_harness() {
    /* data structure */
    struct aws_linked_list_node after;
    struct aws_linked_list_node after_next;
    struct aws_linked_list_node to_add;

    after.next = &after_next;
    after_next.prev = &after;

    /* perform operation under verification */
    aws_linked_list_insert_after(&after, &to_add);

    /* assertions */
    assert(aws_linked_list_node_next_is_valid(&after));
    assert(aws_linked_list_node_prev_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&to_add));
    assert(aws_linked_list_node_prev_is_valid(&after_next));

    assert(after.next == &to_add);
    assert(after_next.prev == &to_add);
}
