/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_cursor_advance_harness() {
    /* data structure */
    struct aws_byte_cursor cursor;
    size_t len;

    /* assumptions */
    ensure_byte_cursor_has_allocated_buffer_member(&cursor);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cursor));

    /* save current state of cursor */
    uint8_t *debug_ptr = cursor.ptr;
    size_t debug_len = cursor.len;
    struct aws_byte_cursor old = cursor;
    struct store_byte_from_buffer old_byte_from_cursor;
    save_byte_from_array(cursor.ptr, cursor.len, &old_byte_from_cursor);

    /* operation under verification */
    struct aws_byte_cursor rv = aws_byte_cursor_advance(&cursor, len);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&rv));
    if (old.len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || len > old.len) {
        assert(rv.ptr == NULL);
        assert(rv.len == 0);
        if (old.len != 0) {
            assert_byte_from_buffer_matches(cursor.ptr, &old_byte_from_cursor);
        }
    } else {
        assert(rv.ptr == old.ptr);
        assert(rv.len == len);
        assert(cursor.ptr == old.ptr + len);
        assert(cursor.len == old.len - len);
    }
}
