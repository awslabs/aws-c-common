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

void __CPROVER_file_local_priority_queue_c_s_swap(struct aws_priority_queue *queue, size_t a, size_t b);

void aws_priority_queue_s_swap_harness() {
    /* Data structure */
    struct aws_priority_queue queue;

    /* Assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);

    /* Assume the function preconditions */
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));
    size_t a;
    size_t b;
    __CPROVER_assume(a < queue.container.length);
    __CPROVER_assume(b < queue.container.length);

    if (queue.backpointers.data) {
        /* Assume that the two backpointers a, b are valid, either by
         * being NULL or by allocating their objects with their correct
         * values. */
        ((struct aws_priority_queue_node **)queue.backpointers.data)[a] =
            can_fail_malloc(sizeof(struct aws_priority_queue_node));
        ((struct aws_priority_queue_node **)queue.backpointers.data)[b] =
            can_fail_malloc(sizeof(struct aws_priority_queue_node));
    }

    /* Perform operation under verification */
    __CPROVER_file_local_priority_queue_c_s_swap(&queue, a, b);

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));
}
