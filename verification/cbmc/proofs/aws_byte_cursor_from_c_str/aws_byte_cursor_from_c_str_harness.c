/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_from_c_str_harness() {
    /* parameters */
    const char *c_str = ensure_c_str_is_allocated(MAX_BUFFER_SIZE);

    /* operation under verification */
    struct aws_byte_cursor cur = aws_byte_cursor_from_c_str(c_str);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    if (cur.ptr) { /* if ptr is NULL len shoud be 0, otherwise equal to c_str */
        assert(cur.len == strlen(c_str));
        assert_bytes_match(cur.ptr, (uint8_t *)c_str, cur.len);
    } else {
        assert(cur.len == 0);
    }
}
