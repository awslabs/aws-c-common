/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_byte_buf_reset_harness() {
    struct aws_byte_buf buf;

    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    struct aws_byte_buf old = buf;
    bool zero_contents;
    aws_byte_buf_reset(&buf, zero_contents);
    assert(buf.len == 0);
    assert(buf.allocator == old.allocator);
    assert(buf.buffer == old.buffer);
    assert(buf.capacity == old.capacity);
    if (zero_contents) {
        assert_all_bytes_are(buf.buffer, 0, buf.capacity);
    }
}
