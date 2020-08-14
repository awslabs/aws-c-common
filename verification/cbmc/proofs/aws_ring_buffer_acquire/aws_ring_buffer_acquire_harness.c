/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/ring_buffer_abstract_states.h>

void aws_ring_buffer_acquire_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_ring_buffer ring_buf;

    size_t requested_size;
    size_t ring_buf_size;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* copy of state before call */
    struct aws_ring_buffer ring_buf_old = ring_buf;

    int result = aws_ring_buffer_acquire(&ring_buf, requested_size, &buf);

    /* assertions */
    uint8_t *old_head = aws_atomic_load_ptr(&ring_buf_old.head);
    uint8_t *old_tail = aws_atomic_load_ptr(&ring_buf_old.tail);
    uint8_t *new_head = aws_atomic_load_ptr(&ring_buf.head);
    uint8_t *new_tail = aws_atomic_load_ptr(&ring_buf.tail);
    if (result == AWS_OP_SUCCESS) {
        assert(aws_byte_buf_is_valid(&buf));
        assert(buf.capacity == requested_size);
        assert(AWS_MEM_IS_WRITABLE(buf.buffer, buf.capacity));
        assert(buf.len == 0); /* aws_byte_buf always created with aws_byte_buf_from_empty_array */
        assert(aws_ring_buffer_buf_belongs_to_pool(&ring_buf, &buf));
        if (aws_ring_buffer_is_empty(&ring_buf_old)) {
            assert(new_head == ring_buf_old.allocation + requested_size);
            assert(new_tail == ring_buf_old.allocation);
        } else {
            assert(new_head == ring_buf_old.allocation + requested_size || new_head == old_head + requested_size);
            assert(new_tail == old_tail);
        }
        assert(IMPLIES(is_empty_state(&ring_buf_old), is_front_valid_state(&ring_buf)));
        assert(IMPLIES(is_front_valid_state(&ring_buf_old), is_front_valid_state(&ring_buf)));
        assert(IMPLIES(
            is_middle_valid_state(&ring_buf_old), is_middle_valid_state(&ring_buf) || is_ends_valid_state(&ring_buf)));
        assert(IMPLIES(is_ends_valid_state(&ring_buf_old), is_ends_valid_state(&ring_buf)));
        assert(!(is_front_valid_state(&ring_buf_old) && is_middle_valid_state(&ring_buf)));
    } else {
        assert(ring_buf == ring_buf_old);
    }
    assert(aws_ring_buffer_is_valid(&ring_buf));
    assert(ring_buf.allocator == ring_buf_old.allocator);
    assert(ring_buf.allocation == ring_buf_old.allocation);
    assert(ring_buf.allocation_end == ring_buf_old.allocation_end);
}
