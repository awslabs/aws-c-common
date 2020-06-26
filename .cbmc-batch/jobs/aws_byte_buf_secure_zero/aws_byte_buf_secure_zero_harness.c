/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_secure_zero_harness() {
    struct aws_byte_buf buf;

    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* operation under verification */
    aws_byte_buf_secure_zero(&buf);

    assert(aws_byte_buf_is_valid(&buf));
    assert_all_zeroes(buf.buffer, buf.capacity);
    assert(buf.len == 0);
}
