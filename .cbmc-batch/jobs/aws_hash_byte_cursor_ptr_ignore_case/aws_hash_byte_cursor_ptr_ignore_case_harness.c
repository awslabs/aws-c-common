/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_hash_byte_cursor_ptr_ignore_case_harness() {
    /* parameters */
    struct aws_byte_cursor cur;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));
    __CPROVER_assume(AWS_MEM_IS_READABLE(cur.ptr, cur.len));

    /* operation under verification */
    aws_hash_byte_cursor_ptr_ignore_case(&cur);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
}
