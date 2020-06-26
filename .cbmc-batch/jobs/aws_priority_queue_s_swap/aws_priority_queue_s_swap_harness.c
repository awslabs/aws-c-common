/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
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

    /* save current state of the data structure */
    struct aws_array_list old = queue.container;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array((uint8_t *)old.data, old.current_size, &old_byte);

    size_t item_sz = queue.container.item_size;
    size_t offset;
    __CPROVER_assume(offset < item_sz);
    /* save a byte of the element at index a */
    struct store_byte_from_buffer old_a_byte;
    old_a_byte.index = a * item_sz + offset;
    old_a_byte.byte = ((uint8_t *)queue.container.data)[old_a_byte.index];

    /* save a byte of the element at index b */
    struct store_byte_from_buffer old_b_byte;
    old_b_byte.index = b * item_sz + offset;
    old_b_byte.byte = ((uint8_t *)queue.container.data)[old_b_byte.index];

    /* Perform operation under verification */
    __CPROVER_file_local_priority_queue_c_s_swap(&queue, a, b);

    /* Assert the postconditions */
    assert(aws_priority_queue_is_valid(&queue));

    /* All the elements in the container except for a and b should stay unchanged */
    size_t ob_i = old_byte.index;
    if (ob_i < a * item_sz && ob_i >= (a + 1) * item_sz && ob_i < b * item_sz && ob_i >= (b + 1) * item_sz) {
        assert_array_list_equivalence(&queue.container, &old, &old_byte);
    }
    /* The new element at index a must be equal to the old element in index b and vice versa */
    assert(old_a_byte.byte == ((uint8_t *)queue.container.data)[old_b_byte.index]);
    assert(old_b_byte.byte == ((uint8_t *)queue.container.data)[old_a_byte.index]);
}
