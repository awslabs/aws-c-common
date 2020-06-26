/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_ring_buffer_clean_up_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    size_t ring_buf_size;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));

    /* operation under verification */
    aws_ring_buffer_clean_up(&ring_buf);

    /* assertions */
    assert(ring_buf.allocator == NULL);
    assert(ring_buf.allocation == NULL);
    assert(aws_atomic_load_ptr(&ring_buf.head) == NULL);
    assert(aws_atomic_load_ptr(&ring_buf.tail) == NULL);
    assert(ring_buf.allocation_end == NULL);
}
