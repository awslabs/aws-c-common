/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/ring_buffer_abstract_states.h>

void aws_ring_buffer_release_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_ring_buffer ring_buf;

    size_t ring_buf_size;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    __CPROVER_assume(!aws_ring_buffer_is_empty(&ring_buf));
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    ensure_byte_buf_has_allocated_buffer_member_in_ring_buf(&buf, &ring_buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* copy of state before call */
    struct aws_ring_buffer ring_buf_old = ring_buf;
    struct aws_byte_buf buf_old = buf;

    aws_ring_buffer_release(&ring_buf, &buf);

    /* assertions */
    uint8_t *old_head = aws_atomic_load_ptr(&ring_buf_old.head);
    uint8_t *old_tail = aws_atomic_load_ptr(&ring_buf_old.tail);
    uint8_t *new_head = aws_atomic_load_ptr(&ring_buf.head);
    uint8_t *new_tail = aws_atomic_load_ptr(&ring_buf.tail);
    assert(aws_ring_buffer_is_valid(&ring_buf));
    assert(ring_buf.allocator == ring_buf_old.allocator);
    assert(ring_buf.allocation == ring_buf_old.allocation);
    assert(new_head == old_head);
    assert(new_tail == buf_old.buffer + buf_old.capacity);
    assert(ring_buf.allocation_end == ring_buf_old.allocation_end);
    assert(buf.allocator == NULL);
    assert(buf.buffer == NULL);
    assert(buf.len == 0);
    assert(buf.capacity == 0);
    assert(IMPLIES(is_front_valid_state(&ring_buf_old), is_empty_state(&ring_buf) || is_middle_valid_state(&ring_buf)));
    assert(IMPLIES(
        is_middle_valid_state(&ring_buf_old),
        is_empty_state(&ring_buf) || is_middle_valid_state(&ring_buf) || is_ends_valid_state(&ring_buf)));
    assert(IMPLIES(
        is_ends_valid_state(&ring_buf_old),
        is_empty_state(&ring_buf) || is_middle_valid_state(&ring_buf) || is_ends_valid_state(&ring_buf)));
}
