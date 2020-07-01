/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_write_be32_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    uint32_t x;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    /* operation under verification */
    if (aws_byte_buf_write_be32(&buf, x)) {
        assert(buf.len == old.len + 4);
        assert(old.capacity == buf.capacity);
        assert(old.allocator == buf.allocator);
    } else {
        assert_byte_buf_equivalence(&buf, &old, &old_byte_from_buf);
    }

    assert(aws_byte_buf_is_valid(&buf));
}
