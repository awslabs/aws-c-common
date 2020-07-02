/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 13s
 */
void aws_priority_queue_size_harness() {
    /* data structure */
    struct aws_priority_queue queue;

    /* assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));

    /* save current state of the container structure */
    struct aws_array_list old_container = queue.container;
    struct store_byte_from_buffer old_byte_container;
    save_byte_from_array((uint8_t *)old_container.data, old_container.current_size, &old_byte_container);

    /* save current state of the backpointers structure */
    struct aws_array_list old_backpointers = queue.backpointers;
    struct store_byte_from_buffer old_byte_backpointers;
    save_byte_from_array((uint8_t *)old_backpointers.data, old_backpointers.current_size, &old_byte_backpointers);

    /* perform operation under verification */
    size_t size = aws_priority_queue_size(&queue);

    /* assertions */
    assert(aws_priority_queue_is_valid(&queue));
    assert_array_list_equivalence(&queue.container, &old_container, &old_byte_container);
    assert_array_list_equivalence(&queue.backpointers, &old_backpointers, &old_byte_backpointers);
}
