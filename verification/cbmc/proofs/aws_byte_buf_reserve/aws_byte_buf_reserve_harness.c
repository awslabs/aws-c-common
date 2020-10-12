/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_reserve_harness() {
    struct aws_byte_buf buf;
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    struct aws_byte_buf old = buf;
    size_t requested_capacity;

    if (aws_byte_buf_reserve(&buf, requested_capacity) == AWS_OP_SUCCESS) {
        assert(buf.capacity >= requested_capacity);
        assert(aws_byte_buf_has_allocator(&buf));
        assert(aws_byte_buf_is_valid(&buf));
    }

    assert(old.len == buf.len);
    assert(old.allocator == buf.allocator);
    if (!buf.buffer) {
        assert_bytes_match(old.buffer, buf.buffer, buf.len);
    }
}
