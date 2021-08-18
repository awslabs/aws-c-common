/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: s_swap
 *
 * This function overrides s_swap and only swaps the backpointer
 * indexes. It is used to improve the running time of the CBMC proofs,
 * as this function adds heavy overhead on the proofs, especially the
 * ones that loop over the elements of the priority queue (such as
 * s_sift_up, s_sift_down, s_sift_either).
 *
 * It is safe to stub s_swap out, as long as no assertions about the
 * values of the elements in the priority queue are made
 * afterwards. Therefore, this stub cannot be used in proofs about the
 * order of the elements in the priority queue, or any other
 * functional correctness property concerning the values of the
 * elements in the queue.
 *
 */

#include <aws/common/priority_queue.h>

void __CPROVER_file_local_priority_queue_c_s_swap(struct aws_priority_queue *queue, size_t a, size_t b) {
    assert(aws_priority_queue_is_valid(queue));
    assert(a < queue->container.length);
    assert(b < queue->container.length);
    assert(aws_priority_queue_backpointer_index_valid(queue, a));
    assert(aws_priority_queue_backpointer_index_valid(queue, b));

    if (queue->backpointers.data) {
        assert(queue->backpointers.length > a);
        assert(queue->backpointers.length > b);
    }
}
