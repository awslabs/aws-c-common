/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_byte_cursor_read_u8_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    size_t length;
    __CPROVER_assume(length >= 1);
    uint8_t *dest = bounded_malloc(length);

    /* assumptions */
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* precondition */
    __CPROVER_assume(AWS_MEM_IS_WRITABLE(dest, 1));

    /* save current state of the data structure */
    struct aws_byte_cursor old_cur = cur;
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);

    /* operation under verification */
    if (aws_byte_cursor_read_u8(&cur, dest)) {
        assert_bytes_match(old_cur.ptr, dest, 1);
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    /* the following assertions are included, because aws_byte_cursor_read internally uses
     * aws_byte_cursor_advance_nospec and it copies the bytes from the advanced cursor to *dest
     */
    if (old_cur.len < (SIZE_MAX >> 1) && old_cur.len > 1) {
        assert(cur.ptr == old_cur.ptr + 1);
        assert(cur.len == old_cur.len - 1);
    }
}
