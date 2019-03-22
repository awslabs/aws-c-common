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

const size_t MAX_STRING_LEN = 16;

/**
 * Coverage:1.00 (70 lines out of 70 statically-reachable lines in 14 functions reached)
 * Runtime: real	0m7.394s
 */

void aws_byte_buf_write_from_whole_string_harness() {
    struct aws_byte_buf *buf = allocate_arbitrary_byte_buf_nondet_len_max(can_fail_allocator(), MAX_STRING_LEN);
    struct aws_byte_buf old_buf = *buf;
    // nondeterministially pick a byte. We can then track if it has changed
    size_t index_to_check = nondet_size_t();
    __CPROVER_assume(index_to_check < buf->len);
    uint8_t byte_old = buf->buffer[index_to_check];
    size_t availabie_cap = buf->capacity - buf->len;
    struct aws_string *str = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);

    bool rval = aws_byte_buf_write_from_whole_string(buf, str);
    // The value is appended to the end of the byte buf.  Make sure that worked.
    if (rval) {
        assert(availabie_cap >= str->len);
        assert(buf->len == str->len + old_buf.len);
        assert_bytes_match(str->bytes, buf->buffer + old_buf.len, str->len);
    } else {
        assert(availabie_cap < str->len);
    }
    // In either case, the existing bytes in the buffer were unchanged.
    assert(buf->buffer[index_to_check] == byte_old);
}
