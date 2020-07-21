/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_priority_queue_pop_harness() {
    /* Data structure */
    struct aws_priority_queue queue;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);

    /* Assume the function preconditions */
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    void *item = can_fail_malloc(queue.container.item_size);

    if (queue.backpointers.data) {
        /* Assume that the two backpointers 0, len-1 are valid,
         * either by being NULL or by allocating their objects. This
         * is important for the s_swap that happens in s_remove. */
        size_t len = queue.backpointers.length;
        if (0 < len) {
            ((struct aws_priority_queue_node **)queue.backpointers.data)[0] =
                can_fail_malloc(sizeof(struct aws_priority_queue_node));
            if (0 != len - 1) {
                ((struct aws_priority_queue_node **)queue.backpointers.data)[len - 1] =
                    can_fail_malloc(sizeof(struct aws_priority_queue_node));
            }
        }
    }

    /* Save the old priority queue state */
    struct aws_priority_queue old_queue = queue;

    /* Assume the preconditions */
    __CPROVER_assume(item && AWS_MEM_IS_WRITABLE(item, queue.container.item_size));

    /* Perform operation under verification */
    if (aws_priority_queue_pop(&queue, item) == AWS_OP_SUCCESS) {
        assert(old_queue.container.length == 1 + queue.container.length);
        if (queue.backpointers.data) {
            assert(old_queue.backpointers.length == 1 + queue.backpointers.length);
        }
    }

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
}
