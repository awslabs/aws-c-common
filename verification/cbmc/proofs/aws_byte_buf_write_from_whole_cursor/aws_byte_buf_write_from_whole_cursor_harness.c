/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_write_from_whole_cursor_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_byte_cursor src;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));
    __CPROVER_assume(aws_byte_cursor_is_bounded(&src, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&src);
    __CPROVER_assume(aws_byte_cursor_is_valid(&src));

    /* save current state of the parameters */
    struct aws_byte_buf buf_old = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);
    struct aws_byte_cursor src_old = src;
    struct store_byte_from_buffer old_byte_from_src;
    save_byte_from_array(src.ptr, src.len, &old_byte_from_src);

    /* operation under verification */
    if (aws_byte_buf_write_from_whole_cursor(&buf, src)) {
        assert(buf.len == buf_old.len + src.len);
        assert(buf_old.capacity == buf.capacity);
        assert(buf_old.allocator == buf.allocator);
        if (src.len > 0 && buf.len > 0) {
            assert_bytes_match(buf.buffer + buf_old.len, src.ptr, src.len);
        }
    } else {
        assert_byte_buf_equivalence(&buf, &buf_old, &old_byte_from_buf);
    }

    assert(aws_byte_buf_is_valid(&buf));
    assert(aws_byte_cursor_is_valid(&src));
    assert_byte_cursor_equivalence(&src, &src_old, &old_byte_from_src);
}
