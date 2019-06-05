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

void aws_byte_cursor_read_be64_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    size_t length;
    uint64_t *dest = can_fail_malloc(length);

    /* assumptions */
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));

    /* save current state of the data structure */
    struct aws_byte_cursor old_cur = cur;
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);

    /* operation under verification */
    if (aws_byte_cursor_read_be64((nondet_bool() ? &cur : NULL), dest)) {
        uint64_t dest_copy;
        memcpy(&dest_copy, old_cur.ptr, 8);
        dest_copy = aws_ntoh64(dest_copy);
        assert_bytes_match((uint8_t *)&dest_copy, (uint8_t *)dest, 8);
        /* the following assertions are included, because aws_byte_cursor_read internally uses
         * aws_byte_cursor_advance_nospec and it copies the bytes from the advanced cursor to *dest
         */
        assert(8 <= old_cur.len && old_cur.len <= (SIZE_MAX >> 1));
        assert(cur.ptr == old_cur.ptr + 8);
        assert(cur.len == old_cur.len - 8);
    } else {
        assert(cur.len == old_cur.len);
        if (cur.len != 0) {
            assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cur);
        }
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
}
