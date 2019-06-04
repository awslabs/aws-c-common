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

void aws_byte_cursor_eq_byte_buf_harness() {
    /* parameters */
    struct aws_byte_cursor cur;
    struct aws_byte_buf buf;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cur, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cur);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cur));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the data structure */
    struct aws_byte_cursor old_cur = cur;
    struct store_byte_from_buffer old_byte_from_cur;
    save_byte_from_array(cur.ptr, cur.len, &old_byte_from_cur);
    struct aws_byte_buf old_buf = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    /* operation under verification */
    if (aws_byte_cursor_eq_byte_buf((nondet_bool() ? &cur : NULL), (nondet_bool() ? &buf : NULL))) {
        assert(cur.len == buf.len);
        if (cur.len > 0) {
            assert_bytes_match(cur.ptr, buf.buffer, cur.len);
        }
    }

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    assert(aws_byte_buf_is_valid(&buf));
    if (cur.len > 0) {
        assert_byte_from_buffer_matches(cur.ptr, &old_byte_from_cur);
    }
    assert_byte_buf_equivalence(&buf, &old_buf, &old_byte_from_buf);
}
