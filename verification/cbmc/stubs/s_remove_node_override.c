/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * FUNCTION: s_remove_node
 *
 * This function overrides the original implementation of the
 * s_remove_node function from priority_queue.h with a no_op.
 *
 * It is safe to use as long as there are no assertions on the
 * positions of elements in the priority queue after its invocation,
 * as it doesn't really remove an element and reorders the rest, but
 * it just reduces the length of both of the array lists of the
 * priority queue by 1.
 */

#include <aws/common/priority_queue.h>

int __CPROVER_file_local_priority_queue_c_s_remove_node(
    struct aws_priority_queue *queue,
    void *item,
    size_t item_index) {
    assert(aws_priority_queue_is_valid(queue));
    assert(item && AWS_MEM_IS_WRITABLE(item, queue->container.item_size));

    /* If aws_array_list_get_at succeeds, it means that the item_index
     * is in range of the container, and thus the queue has at least
     * item_index + 1 elements */
    if (aws_array_list_get_at(&queue->container, item, item_index)) {
        /* shouldn't happen, but if it does we've already raised an error... */
        assert(aws_priority_queue_is_valid(queue));
        return AWS_OP_ERR;
    }

    /* This can never underflow, as aws_array_list_get_at has
     * succeeded, which means that the container has at least one
     * item. Also if the backpointers array_list is initialized, it is
     * constrained to have the same length as the container array_list
     * (as queue is a valid priority queue) and thus is guaranteed to
     * not underflow. */
    queue->container.length -= 1;
    if (queue->backpointers.data) {
        queue->backpointers.length -= 1;
    }

    assert(aws_priority_queue_is_valid(queue));
    return AWS_OP_SUCCESS;
}
