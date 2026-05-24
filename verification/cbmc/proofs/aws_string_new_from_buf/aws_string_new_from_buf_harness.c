/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_string_new_from_buf_harness() {
    /* parameters */
    struct aws_allocator *allocator;
    struct aws_byte_buf buf;

    /* precondition */
    ASSUME_DEFAULT_ALLOCATOR(allocator);
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* operation under verification */
    struct aws_string *str = aws_string_new_from_buf(allocator, &buf);

    /* assertions */
    if (str) {
        assert(str->len == buf.len);
        assert(str->bytes[str->len] == 0);
        assert_bytes_match(str->bytes, buf.buffer, str->len);
        assert(aws_string_is_valid(str));
    }
}

