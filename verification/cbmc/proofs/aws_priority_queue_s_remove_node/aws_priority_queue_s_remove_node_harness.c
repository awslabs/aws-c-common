/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

int __CPROVER_file_local_priority_queue_c_s_remove_node(struct aws_priority_queue *queue, void *item, size_t index);

void aws_priority_queue_s_remove_node_harness() {
    /* Data structure */
    struct aws_priority_queue queue;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);

    /* Assume the function preconditions */
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    void *item = malloc(queue.container.item_size);
    size_t index;
    __CPROVER_assume(index < queue.container.length);

    struct aws_priority_queue_node *node = malloc(sizeof(struct aws_priority_queue_node));

    if (queue.backpointers.data) {
        /* Assume that the two backpointers index, len-1 are valid,
         * either by being NULL or by allocating their objects. This
         * is important for the s_swap that happens in s_remove. */
        size_t len = queue.backpointers.length;
        if (index < len) {
            ((struct aws_priority_queue_node **)queue.backpointers.data)[index] = node;
            if (index != len - 1) {
                ((struct aws_priority_queue_node **)queue.backpointers.data)[len - 1] =
                    malloc(sizeof(struct aws_priority_queue_node));
            }
        }
    }

    /* Save the old priority queue state */
    struct aws_priority_queue old_queue = queue;

    /* Assume the preconditions */
    __CPROVER_assume(item && AWS_MEM_IS_WRITABLE(item, queue.container.item_size));

    /* Perform operation under verification */
    if (__CPROVER_file_local_priority_queue_c_s_remove_node(&queue, item, index) == AWS_OP_SUCCESS) {
        assert(old_queue.container.length == 1 + queue.container.length);
        if (queue.backpointers.data) {
            assert(old_queue.backpointers.length == 1 + queue.backpointers.length);
            if (node) {
                /* The node pointing in the element of the priority queue
                 * now points to SIZE_MAX to indicate that the item was
                 * removed */
                assert(node->current_index == SIZE_MAX);
            }
        }
    }

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
}
