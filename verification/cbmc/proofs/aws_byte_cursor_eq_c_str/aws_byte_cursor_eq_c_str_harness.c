/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_eq_c_str_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    const char *c_str = ensure_c_str_is_allocated(MAX_BUFFER_SIZE);

    /* assumptions */
    __CPROVER_assume(c_str != NULL);
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* save current state of the parameters */
    struct aws_byte_cursor old = cur;
    struct store_byte_from_buffer old_byte_from_cursor;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cursor);
    size_t str_len = strlen(c_str);
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
