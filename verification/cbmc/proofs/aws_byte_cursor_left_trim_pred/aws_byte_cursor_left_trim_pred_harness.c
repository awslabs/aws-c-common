/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_left_trim_pred_harness() {
    /* parameters */
    struct aws_byte_cursor cur;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* save current state of the data structure */
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);

    /* operation under verification */
    struct aws_byte_cursor rv = aws_byte_cursor_left_trim_pred(&cur, uninterpreted_predicate_fn);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    assert(aws_byte_cursor_is_valid(&rv));
    if (cur.len > 0) {
        assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cur);
    }
}
