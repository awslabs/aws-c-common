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

void aws_byte_buf_init_copy_from_cursor_harness() {
    /* data structure */
    struct aws_byte_buf buf;

    /* parameters */
    struct aws_allocator *allocator;
    struct aws_byte_cursor cursor;

    /* assumptions */
    __CPROVER_assume(aws_byte_cursor_is_bounded(&cursor, MAX_BUFFER_SIZE));
    ensure_byte_cursor_has_allocated_buffer_member(&cursor);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cursor));

    ASSUME_CAN_FAIL_ALLOCATOR(allocator);

    if (aws_byte_buf_init_copy_from_cursor(&buf, allocator, cursor) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_byte_buf_is_valid(&buf));
        assert(aws_byte_cursor_is_valid(&cursor));
        assert(buf.len == cursor.len);
        assert(buf.capacity == cursor.len);
        assert(buf.allocator == allocator);
        if (buf.buffer) {
            assert_bytes_match(buf.buffer, cursor.ptr, buf.len);
        }
    }
}
