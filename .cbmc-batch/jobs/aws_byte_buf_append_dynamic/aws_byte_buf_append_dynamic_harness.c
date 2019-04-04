/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

void aws_byte_buf_append_dynamic_harness() {
    struct aws_byte_buf to;
    __CPROVER_assume(aws_byte_buf_is_valid(&to));
    ensure_byte_buf_has_allocated_buffer_member(&to);

    struct aws_byte_cursor from;
    __CPROVER_assume(aws_byte_cursor_is_valid(&from));
    ensure_byte_cursor_has_allocated_buffer_member(&from);

    aws_byte_buf_append_dynamic(&to, &from);

    assert(aws_byte_buf_is_valid(&to));
    assert(is_byte_buf_expected_alloc(&to));
    assert(aws_byte_cursor_is_valid(&from));
}
