/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_string_eq_byte_buf_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    struct aws_byte_buf buf;

    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_STRING_LEN));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    if (aws_string_eq_byte_buf(str, nondet_bool() ? &buf : NULL) && str) {
        assert(str->len == buf.len);
        assert_bytes_match(str->bytes, buf.buffer, str->len);
        assert(aws_string_is_valid(str));
    }

    assert(aws_byte_buf_is_valid(&buf));
}
