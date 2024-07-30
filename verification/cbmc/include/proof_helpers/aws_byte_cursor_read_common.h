/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_read_common_harness(void) {
    /* parameters */
    struct aws_byte_cursor cur;
    DEST_TYPE *dest = malloc(sizeof(*dest));

    /* assumptions */
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));
    __CPROVER_assume(cur.len >= BYTE_WIDTH);
    __CPROVER_assume(AWS_MEM_IS_READABLE(cur.ptr, BYTE_WIDTH));
    __CPROVER_assume(dest != NULL);

    /* save current state of the data structure */
    struct aws_byte_cursor old_cur = cur;
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);
    DEST_TYPE dest_copy;
    memcpy(&dest_copy, old_cur.ptr, BYTE_WIDTH);
    dest_copy = AWS_NTOH(dest_copy);

    /* operation under verification */
    if (BYTE_CURSOR_READ(&cur, dest)) {
        assert_bytes_match((uint8_t *)&dest_copy, (uint8_t *)dest, BYTE_WIDTH);
        /* the following assertions are included, because aws_byte_cursor_read internally uses
         * aws_byte_cursor_advance_nospec and it copies the bytes from the advanced cursor to *dest
         */
        assert(BYTE_WIDTH <= old_cur.len && old_cur.len <= (SIZE_MAX >> 1));
        assert(cur.ptr == old_cur.ptr + BYTE_WIDTH);
        assert(cur.len == old_cur.len - BYTE_WIDTH);
    } else {
        assert(cur.len == old_cur.len);
        if (cur.len != 0) {
            assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cur);
        }
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
}
