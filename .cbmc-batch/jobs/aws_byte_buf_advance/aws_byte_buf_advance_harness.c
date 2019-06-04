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

void aws_byte_buf_advance_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    struct aws_byte_buf output;
    size_t len;

    /* assumptions */
    __CPROVER_assume(aws_byte_buf_is_bounded(&buf, MAX_BUFFER_SIZE));
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));
    if (nondet_bool()) {
        output = buf;
    } else {
        __CPROVER_assume(aws_byte_buf_is_bounded(&output, MAX_BUFFER_SIZE));
        ensure_byte_buf_has_allocated_buffer_member(&output);
        __CPROVER_assume(aws_byte_buf_is_valid(&output));
    }

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    /* operation under verification */
    if (aws_byte_buf_advance((nondet_bool() ? &buf : NULL), (nondet_bool() ? &output : NULL), len)) {
        assert(buf.len == old.len + len);
        assert(buf.capacity == old.capacity);
        assert(buf.allocator == old.allocator);
        if (old.len > 0) {
            assert_byte_from_buffer_matches(buf.buffer, &old_byte_from_buf);
        }
        assert(output.len == 0);
        assert(output.capacity == len);
        assert(output.allocator == NULL);
    } else {
        assert_byte_buf_equivalence(&buf, &old, &old_byte_from_buf);
        assert(output.len == 0);
        assert(output.capacity == 0);
        assert(output.allocator == NULL);
        assert(output.buffer == NULL);
    }
    assert(aws_byte_buf_is_valid(&buf));
    assert(aws_byte_buf_is_valid(&output));
}
