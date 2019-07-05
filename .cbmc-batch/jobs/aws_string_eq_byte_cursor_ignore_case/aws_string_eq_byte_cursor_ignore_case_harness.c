/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_string_eq_byte_cursor_ignore_case_harness() {
    struct aws_string *str = nondet_bool() ? ensure_string_is_allocated_bounded_length(MAX_STRING_LEN) : NULL;
    struct aws_byte_cursor cursor;

    ensure_byte_cursor_has_allocated_buffer_member(&cursor);
    __CPROVER_assume(aws_byte_cursor_is_valid(&cursor));

    bool nondet_parameter;
    if (aws_string_eq_byte_cursor_ignore_case(str, nondet_parameter ? &cursor : NULL) && str) {
        assert(aws_string_is_valid(str));
        if (nondet_parameter) {
            assert(str->len == cursor.len);
        }
    }
    assert(aws_byte_cursor_is_valid(&cursor));
}
