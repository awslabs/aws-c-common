/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

void __CPROVER_file_local_priority_queue_c_s_sift_up(struct aws_priority_queue *queue, size_t root);

void aws_priority_queue_s_sift_up_harness() {
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
    __CPROVER_file_local_priority_queue_c_s_sift_up(&queue, root);

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
    assert(aws_priority_queue_backpointers_valid_deep(&queue));
}
