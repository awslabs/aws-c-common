/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_byte_buf_write_from_whole_string_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    struct aws_byte_buf buf;

    ensure_byte_buf_has_allocated_buffer_member(&buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    /* save current state of the data structure */
    struct aws_byte_buf old_buf = buf;
    struct store_byte_from_buffer old_byte_from_buf;
    save_byte_from_array(buf.buffer, buf.len, &old_byte_from_buf);

    size_t available_cap = buf.capacity - buf.len;
    bool nondet_parameter;

    if (aws_byte_buf_write_from_whole_string(nondet_parameter ? &buf : NULL, str) && str) {
        assert(aws_string_is_valid(str));
        assert(available_cap >= str->len);
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
