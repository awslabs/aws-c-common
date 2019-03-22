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
 * Coverage: 1.00 (57 lines out of 57 statically-reachable lines in 11 functions reached)
 * Runtime: real	0m4.590s
 */
void aws_string_eq_byte_buffer_harness() {
    struct aws_string *str = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
    struct aws_byte_buf *buf = allocate_arbitrary_byte_buf_nondet_len_max(can_fail_allocator(), MAX_STRING_LEN);
    bool rval = aws_string_eq_byte_buf(str, buf);
    if (rval) {
        assert(str->len == buf->len);
        assert_bytes_match(str->bytes, buf->buffer, str->len);
    }
}
