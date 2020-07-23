/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_buf_eq_ignore_case_harness() {
    /* parameters */
    struct aws_byte_buf lhs;
    struct aws_byte_buf rhs;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&lhs, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&lhs);
    __CPROVER_assume(aws_byte_buf_is_valid(&lhs));
    if (nondet_bool()) {
        rhs = lhs;
    } else {
        __CPROVER_assume(aws_byte_buf_is_bounded(&rhs, MAX_BUFFER_SIZE));
        ensure_byte_buf_has_allocated_buffer_member(&rhs);
        __CPROVER_assume(aws_byte_buf_is_valid(&rhs));
    }

    /* save current state of the data structure */
    struct aws_byte_buf old_lhs = lhs;
    struct store_byte_from_buffer old_byte_from_lhs;
    save_byte_from_array(lhs.buffer, lhs.len, &old_byte_from_lhs);
    struct aws_byte_buf old_rhs = rhs;
    struct store_byte_from_buffer old_byte_from_rhs;
    save_byte_from_array(rhs.buffer, rhs.len, &old_byte_from_rhs);

    /* operation under verification */
    if (aws_byte_buf_eq_ignore_case(&lhs, &rhs)) {
        assert(lhs.len == rhs.len);
    }

    /* assertions */
    assert(aws_byte_buf_is_valid(&lhs));
    assert(aws_byte_buf_is_valid(&rhs));
    assert_byte_buf_equivalence(&lhs, &old_lhs, &old_byte_from_lhs);
    assert_byte_buf_equivalence(&rhs, &old_rhs, &old_byte_from_rhs);
}
