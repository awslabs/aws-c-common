/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_append_dynamic_harness() {
    struct aws_byte_buf to;
    ensure_byte_buf_has_allocated_buffer_member(&to);
    __CPROVER_assume(aws_byte_buf_is_valid(&to));

    /* save current state of the data structure */
    struct aws_byte_buf to_old = to;

    struct aws_byte_cursor from;
    ensure_byte_cursor_has_allocated_buffer_member(&from);
    __CPROVER_assume(aws_byte_cursor_is_valid(&from));

    /* save current state of the data structure */
    struct aws_byte_cursor from_old = from;

    if (aws_byte_buf_append_dynamic(&to, &from) == AWS_OP_SUCCESS) {
        assert(to.len == to_old.len + from.len);
    } else {
        /* if the operation return an error, to must not change */
        assert_bytes_match(to_old.buffer, to.buffer, to.len);
        assert(to_old.len == to.len);
    }

    assert(aws_byte_buf_is_valid(&to));
    assert(aws_byte_cursor_is_valid(&from));
    assert(to_old.allocator == to.allocator);
    assert_bytes_match(from_old.ptr, from.ptr, from.len);
    assert(from_old.len == from.len);
}
