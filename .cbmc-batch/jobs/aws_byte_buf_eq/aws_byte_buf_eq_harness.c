/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_buf_eq_harness() {
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
    if (aws_byte_buf_eq((nondet_bool() ? &lhs : NULL), (nondet_bool() ? &rhs : NULL))) {
        assert(lhs.len == rhs.len);
        if (lhs.len > 0) {
            assert_bytes_match(lhs.buffer, rhs.buffer, lhs.len);
        }
    }

    /* assertions */
    assert(aws_byte_buf_is_valid(&lhs));
    assert(aws_byte_buf_is_valid(&rhs));
    assert_byte_buf_equivalence(&lhs, &old_lhs, &old_byte_from_lhs);
    assert_byte_buf_equivalence(&rhs, &old_rhs, &old_byte_from_rhs);
}
