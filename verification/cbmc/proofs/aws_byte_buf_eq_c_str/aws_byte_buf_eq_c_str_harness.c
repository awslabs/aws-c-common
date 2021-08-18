/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_eq_c_str_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    const char *c_str = ensure_c_str_is_allocated(MAX_BUFFER_SIZE);

    /* assumptions */
    __CPROVER_assume(aws_c_string_is_valid(c_str));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte;
    save_byte_from_array(buf.buffer, buf.len, &old_byte);
    size_t str_len = strlen(c_str);
    struct store_byte_from_buffer old_byte_from_str;
    save_byte_from_array((uint8_t *)c_str, str_len, &old_byte_from_str);

    /* operation under verification */
    if (aws_byte_buf_eq_c_str(&buf, c_str)) {
        assert(buf.len == str_len);
        if (buf.len > 0) {
            assert_bytes_match(buf.buffer, (uint8_t *)c_str, buf.len);
        }
    }

    /* asserts both parameters remain unchanged */
    assert(aws_byte_buf_is_valid(&buf));
    assert_byte_buf_equivalence(&buf, &old, &old_byte);
    if (str_len > 0) {
        assert_byte_from_buffer_matches((uint8_t *)c_str, &old_byte_from_str);
    }
}
