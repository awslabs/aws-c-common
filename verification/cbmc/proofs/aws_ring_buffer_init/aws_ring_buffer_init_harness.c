/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_ring_buffer_init_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    struct aws_allocator *allocator = can_fail_allocator();
    size_t size;
    __CPROVER_assume(size > 0); /* Precondition */

    if (aws_ring_buffer_init(&ring_buf, allocator, size) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_ring_buffer_is_valid(&ring_buf));
        assert(ring_buf.allocator == allocator);
        assert(ring_buf.allocation_end - ring_buf.allocation == size);
    }
}
