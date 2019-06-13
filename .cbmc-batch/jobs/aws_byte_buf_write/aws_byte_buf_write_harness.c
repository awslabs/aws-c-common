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

void aws_byte_buf_write_harness() {
    /* parameters */
    struct aws_byte_buf buf;
    size_t len;
    uint8_t *array = bounded_malloc(len);

    /* assumptions */
    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the parameters */
    struct aws_byte_buf old = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    if (aws_byte_buf_write(&buf, array, len)) {
        assert(buf.len == old.len + len);
        assert(old.capacity == buf.capacity);
        assert(old.allocator == buf.allocator);
        if (len > 0 && buf.len > 0) {
            assert_bytes_match(buf.buffer + old.len, array, len);
        }
    } else {
        assert_byte_buf_equivalence(&buf, &old, &old_byte_from_buf);
    }

    assert(aws_byte_buf_is_valid(&buf));
}
