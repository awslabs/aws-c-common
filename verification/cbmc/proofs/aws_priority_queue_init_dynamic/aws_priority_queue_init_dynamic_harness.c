/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 9s
 */
void aws_priority_queue_init_dynamic_harness() {

    /* data structure */
    struct aws_priority_queue queue; /* Precondition: queue is non-null */

    /* parameters */
    struct aws_allocator *allocator = aws_default_allocator(); /* Precondition: allocator is non-null */
    size_t item_size;
    size_t initial_item_allocation;
    size_t len;

    /* assumptions */
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    __CPROVER_assume(item_size > 0 && item_size <= MAX_ITEM_SIZE);
    __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));

    /* perform operation under verification */
    uint8_t *raw_array = malloc(len);

    if (aws_priority_queue_init_dynamic(&queue, allocator, initial_item_allocation, item_size, nondet_compare) ==
        AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_priority_queue_is_valid(&queue));
        assert(queue.container.alloc == allocator);
        assert(queue.container.item_size == item_size);
        assert(queue.container.length == 0);
        assert(
            (queue.container.data == NULL && queue.container.current_size == 0) ||
            (queue.container.data && queue.container.current_size == (initial_item_allocation * item_size)));
    } else {
        /* assertions */
        assert(AWS_IS_ZEROED(queue.container));
        assert(AWS_IS_ZEROED(queue.backpointers));
    }
}
