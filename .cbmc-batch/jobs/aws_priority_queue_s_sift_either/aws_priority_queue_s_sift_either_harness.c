/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

void __CPROVER_file_local_priority_queue_c_s_sift_either(struct aws_priority_queue *queue, size_t root);

void aws_priority_queue_s_sift_either_harness() {
    /* Data structure */
    struct aws_priority_queue queue;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_PRIORITY_QUEUE_ITEMS, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);

    /* Assume the function preconditions */
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    size_t root;
    __CPROVER_assume(root < queue.container.length);

    if (queue.backpointers.data) {
        /* Ensuring that just the root cell is correctly allocated is
         * not enough, as the swap requires that both the swapped
         * cells are correctly allocated.  Therefore, if swap is to
         * not be overriden, I have to ensure that all of the root
         * descendants at least are correctly allocated. For now it is
         * ensured that all of them are. */
        size_t i;
        for (i = 0; i < queue.container.length; i++) {
            ((struct aws_priority_queue_node **)queue.backpointers.data)[i] =
                can_fail_malloc(sizeof(struct aws_priority_queue_node));
        }
    }

    /* Perform operation under verification */
    __CPROVER_file_local_priority_queue_c_s_sift_either(&queue, root);

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
    assert(aws_priority_queue_backpointers_valid_deep(&queue));
}
