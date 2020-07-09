/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_byte_cursor_from_string_harness() {
    struct aws_string *str = ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    struct aws_byte_cursor cursor = aws_byte_cursor_from_string(str);
    assert(aws_string_is_valid(str));
    assert(aws_byte_cursor_is_valid(&cursor));
    assert(cursor.len == str->len);
    assert(cursor.ptr == str->bytes);
    assert_bytes_match(str->bytes, cursor.ptr, str->len);
}
