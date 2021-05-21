/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_ring_buffer_init_harness() {
    /* Non-deterministic parameters. */
    struct aws_ring_buffer *ring_buf = malloc(sizeof(*ring_buf));
    struct aws_allocator *allocator = aws_default_allocator();
    size_t size;

    /* Preconditions. */
    __CPROVER_assume(ring_buf != NULL);
    __CPROVER_assume(allocator != NULL);
    __CPROVER_assume(size > 0 && size < MAX_MALLOC);

    /* Operation under verification. */
    if (aws_ring_buffer_init(ring_buf, allocator, size) == AWS_OP_SUCCESS) {
        /* Postconditions. */
        assert(aws_ring_buffer_is_valid(ring_buf));
        assert(ring_buf->allocator == allocator);
        assert(ring_buf->allocation_end - ring_buf->allocation == size);
    }
}
