/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 8s
 */
void aws_priority_queue_init_static_harness() {

    /* data structure */
    struct aws_priority_queue queue; /* Precondition: queue is non-null */

    /* parameters */
    size_t item_size;
    size_t initial_item_allocation;
    size_t len;
    uint8_t *raw_array;

    /* assumptions */
    __CPROVER_assume(initial_item_allocation > 0 && initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    __CPROVER_assume(item_size > 0 && item_size <= MAX_ITEM_SIZE);
    __CPROVER_assume(!aws_mul_size_checked(initial_item_allocation, item_size, &len));

    /* perform operation under verification */
    ASSUME_VALID_MEMORY_COUNT(raw_array, len);
    aws_priority_queue_init_static(&queue, raw_array, initial_item_allocation, item_size, nondet_compare);

    /* assertions */
    assert(aws_priority_queue_is_valid(&queue));
    assert(queue.container.alloc == NULL);
    assert(queue.container.item_size == item_size);
    assert(queue.container.length == 0);
    assert(queue.container.current_size == initial_item_allocation * item_size);
    assert_bytes_match((uint8_t *)queue.container.data, raw_array, len);
}
