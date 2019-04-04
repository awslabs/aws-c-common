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

void aws_byte_buf_reserve_harness() {
    struct aws_byte_buf buf;
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));
    ensure_byte_buf_has_allocated_buffer_member(&buf);

    struct aws_byte_buf old = buf;
    size_t requested_capacity;
    int rval = aws_byte_buf_reserve(&buf, requested_capacity);

    if (rval == AWS_OP_SUCCESS) {
        assert(buf.capacity >= requested_capacity);
    }
    assert(aws_byte_buf_is_valid(&buf));
    assert(is_byte_buf_expected_alloc(&buf));
}
