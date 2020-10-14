/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_string_eq_byte_cursor_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    struct aws_byte_cursor cursor;

    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    ensure_byte_cursor_has_allocated_buffer_member(&cursor);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cursor));

    bool nondet_parameter;
    if (aws_string_eq_byte_cursor(str, nondet_parameter ? &cursor : NULL) && str) {
        assert(aws_string_is_valid(str));
        if (nondet_parameter) {
            assert(str->len == cursor.len);
            if (str->len > 0) {
                assert_bytes_match(str->bytes, cursor.ptr, str->len);
            }
        }
    }
    assert(aws_byte_cursor_is_valid(&cursor));
}
