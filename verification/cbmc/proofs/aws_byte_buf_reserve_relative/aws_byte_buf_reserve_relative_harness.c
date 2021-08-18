/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_reserve_relative_harness() {
    struct aws_byte_buf buf;
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    struct aws_byte_buf old = buf;
    size_t requested_capacity;
    int rval = aws_byte_buf_reserve_relative(&buf, requested_capacity);

    if (rval == AWS_OP_SUCCESS) {
        assert(buf.capacity >= (old.len + requested_capacity));
        assert(aws_byte_buf_has_allocator(&buf));
        assert(aws_byte_buf_is_valid(&buf));
    }
}
