/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_array_eq_harness() {
    /* assumptions */
    size_t lhs_len;
    __CPROVER_assume(lhs_len <= MAX_BUFFER_SIZE);
    void *lhs = malloc(lhs_len);

    void *rhs;
    size_t rhs_len;
    if (nondet_bool()) { /* rhs could be equal to lhs */
        rhs_len = lhs_len;
        rhs = lhs;
    } else {
        __CPROVER_assume(rhs_len <= MAX_BUFFER_SIZE);
        rhs = malloc(rhs_len);
    }

    /* save current state of the parameters */
    struct store_byte_from_buffer old_byte_from_lhs;
    save_byte_from_array((uint8_t *)lhs, lhs_len, &old_byte_from_lhs);
    struct store_byte_from_buffer old_byte_from_rhs;
    save_byte_from_array((uint8_t *)rhs, rhs_len, &old_byte_from_rhs);

    /* pre-conditions */
    __CPROVER_assume((lhs_len == 0) || AWS_MEM_IS_READABLE(lhs, lhs_len));
    __CPROVER_assume((rhs_len == 0) || AWS_MEM_IS_READABLE(rhs, rhs_len));

    /* operation under verification */
    if (aws_array_eq(lhs, lhs_len, rhs, rhs_len)) {
        /* asserts equivalence */
        assert(lhs_len == rhs_len);
        if (lhs_len > 0 && lhs) {
            assert_bytes_match((uint8_t *)lhs, (uint8_t *)rhs, lhs_len);
        }
    }

    /* asserts both parameters remain unchanged */
    if (lhs_len > 0 && lhs) {
        assert_byte_from_buffer_matches((uint8_t *)lhs, &old_byte_from_lhs);
    }
    if (rhs_len > 0 && rhs) {
        assert_byte_from_buffer_matches((uint8_t *)rhs, &old_byte_from_rhs);
    }
}
