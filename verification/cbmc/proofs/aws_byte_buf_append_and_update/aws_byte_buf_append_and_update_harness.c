/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_append_and_update_harness() {
    struct aws_byte_buf to;
    ensure_byte_buf_has_allocated_buffer_member(&to);
    __CPROVER_assume(aws_byte_buf_is_valid(&to));

    /* save current state of the data structure */
    struct aws_byte_buf to_old = to;

    struct aws_byte_cursor from_and_update;
    ensure_byte_cursor_has_allocated_buffer_member(&from_and_update);
    __CPROVER_assume(aws_byte_cursor_is_valid(&from_and_update));

    /* save current state of the data structure */
    struct aws_byte_cursor from_and_update_old = from_and_update;

    if (aws_byte_buf_append_and_update(&to, &from_and_update) == AWS_OP_SUCCESS) {
        assert(to.len == to_old.len + from_and_update.len);
    } else {
        /* if the operation return an error, to must not change */
        assert_bytes_match(to_old.buffer, to.buffer, to.len);
        assert(to_old.len == to.len);
    }

    assert(aws_byte_buf_is_valid(&to));
    assert(aws_byte_cursor_is_valid(&from_and_update));
    assert(to_old.allocator == to.allocator);
    assert(to_old.capacity == to.capacity);
    assert_bytes_match(from_and_update_old.ptr, from_and_update.ptr, from_and_update.len);
    assert(from_and_update_old.len == from_and_update.len);
}
