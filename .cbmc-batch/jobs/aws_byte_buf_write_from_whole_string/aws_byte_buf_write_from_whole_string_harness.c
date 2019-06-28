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
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_byte_buf_write_from_whole_string_harness() {
    struct aws_string *str = nondet_bool() ? ensure_string_is_allocated_bounded_length(MAX_STRING_LEN) : NULL;
    struct aws_byte_buf buf;

    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the data structure */
    struct aws_byte_buf old_buf = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    size_t availabie_cap = buf.capacity - buf.len;
    bool nondet_parameter;

    if (aws_byte_buf_write_from_whole_string(nondet_parameter ? &buf : NULL, str) && str) {
        assert(aws_string_is_valid(str));
        assert(availabie_cap >= str->len);
        if (nondet_parameter) {
            assert(buf.len == old_buf.len + str->len);
            assert(old_buf.capacity == buf.capacity);
            assert(old_buf.allocator == buf.allocator);
            if (str->len > 0 && buf.len > 0) {
                assert_bytes_match(buf.buffer + old_buf.len, str->bytes, str->len);
            }
        }
    } else {
        assert_byte_buf_equivalence(&buf, &old_buf, &old_byte_from_buf);
    }

    assert(aws_byte_buf_is_valid(&buf));
}
