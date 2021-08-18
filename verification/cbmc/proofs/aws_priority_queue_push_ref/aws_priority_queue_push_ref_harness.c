/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_priority_queue_push_ref_harness() {
    /* Data structure */
    struct aws_priority_queue queue;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    void *item = malloc(queue.container.item_size);
    struct aws_priority_queue_node *backpointer = malloc(sizeof(struct aws_priority_queue_node));

    /* Assume the function preconditions */
    __CPROVER_assume(item && AWS_MEM_IS_READABLE(item, queue.container.item_size));

    /* Perform operation under verification */
    aws_priority_queue_push_ref(&queue, item, backpointer);

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
}
