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

void aws_byte_cursor_eq_c_str_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    const char *c_str = make_arbitrary_c_str(MAX_BUFFER_SIZE);

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* save current state of the parameters */
    struct aws_byte_cursor old = cur;
    struct store_byte_from_buffer old_byte_from_cursor;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cursor);
    size_t str_len = (c_str) ? strlen(c_str) : 0;
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* operation under verification */
    if (aws_byte_cursor_eq_c_str(&cur, c_str)) {
        assert(cur.len == str_len);
        if (cur.len > 0) {
            assert_bytes_match(cur.ptr, (uint8_t *)c_str, cur.len);
        }
    }

    /* asserts both parameters remain unchanged */
    assert(aws_byte_cursor_is_valid(&cur));
    if (cur.len > 0) {
        assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cursor);
    }
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
