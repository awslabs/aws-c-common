/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_cursor_eq_harness() {
    /* parameters */
    struct aws_byte_cursor lhs;
    struct aws_byte_cursor rhs;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&lhs, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&lhs);
    __CPROVER_assume(aws_byte_cursor_is_valid(&lhs));
    if (nondet_bool()) {
        rhs = lhs;
    } else {
        __CPROVER_assume(aws_byte_cursor_is_bounded(&rhs, MAX_BUFFER_SIZE));
        ensure_byte_cursor_has_allocated_buffer_member(&rhs);
        __CPROVER_assume(aws_byte_cursor_is_valid(&rhs));
    }

    /* save current state of the data structure */
    struct aws_byte_cursor old_lhs = lhs;
    struct store_byte_from_buffer old_byte_from_lhs;
    save_byte_from_array(lhs.ptr, lhs.len, &old_byte_from_lhs);
    struct aws_byte_cursor old_rhs = rhs;
    struct store_byte_from_buffer old_byte_from_rhs;
    save_byte_from_array(rhs.ptr, rhs.len, &old_byte_from_rhs);

    /* operation under verification */
    if (aws_byte_cursor_eq(&lhs, &rhs)) {
        assert(lhs.len == rhs.len);
        if (lhs.len > 0) {
            assert_bytes_match(lhs.ptr, rhs.ptr, lhs.len);
        }
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&lhs));
    assert(aws_byte_cursor_is_valid(&rhs));
    if (lhs.len != 0) {
        assert_byte_from_buffer_matches(lhs.ptr, &old_byte_from_lhs);
    }
    if (rhs.len != 0) {
        assert_byte_from_buffer_matches(rhs.ptr, &old_byte_from_rhs);
    }
}
