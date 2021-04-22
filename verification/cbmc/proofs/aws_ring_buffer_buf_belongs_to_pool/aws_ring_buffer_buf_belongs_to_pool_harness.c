/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_ring_buffer_buf_belongs_to_pool_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_ring_buffer ring_buf;

    size_t ring_buf_size;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    bool is_member = nondet_bool(); /* nondet assignment required to force true/false */
    if (is_member) {
        __CPROVER_assume(!aws_ring_buffer_is_empty(&ring_buf));
        ensure_byte_buf_has_allocated_buffer_member_in_ring_buf(&buf, &ring_buf);
    } else {
        ensure_byte_buf_has_allocated_buffer_member(&buf);
    }
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    struct aws_ring_buffer ring_buf_old = ring_buf;
    struct aws_byte_buf buf_old = buf;

    bool result = aws_ring_buffer_buf_belongs_to_pool(&ring_buf, &buf);

    /* assertions */
    assert(is_member == result);
    assert(aws_ring_buffer_is_valid(&ring_buf));
    assert(aws_byte_buf_is_valid(&buf));
    assert(ring_buf_old == ring_buf);
    assert(buf_old == buf);
}
