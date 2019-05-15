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

void aws_array_eq_ignore_case_harness() {
    /* parameters */
    void *lhs;
    void *rhs;
    size_t lhs_len;
    size_t rhs_len;

    /* assumptions */
    __CPROVER_assume(lhs_len <= MAX_BUFFER_SIZE);
    lhs = bounded_malloc(lhs_len);
    __CPROVER_assume(rhs_len <= MAX_BUFFER_SIZE);
    rhs = bounded_malloc(rhs_len);

    /* save current state of the parameters */
    struct store_byte_from_buffer old_byte_from_lhs;
    save_byte_from_array((uint8_t *)lhs, lhs_len, &old_byte_from_lhs);
    struct store_byte_from_buffer old_byte_from_rhs;
    save_byte_from_array((uint8_t *)rhs, rhs_len, &old_byte_from_rhs);

    /* operation under verification */
    if (aws_array_eq_ignore_case(lhs, lhs_len, rhs, rhs_len)) {
        assert(lhs_len == rhs_len);
    }

    /* asserts both parameters remain unchanged */
    if (lhs_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)lhs, &old_byte_from_lhs);
    }
    if (rhs_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)rhs, &old_byte_from_rhs);
    }
}
