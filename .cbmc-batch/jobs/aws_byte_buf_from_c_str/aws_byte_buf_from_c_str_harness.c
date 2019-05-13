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

void aws_byte_buf_from_c_str_harness() {
    size_t len;
    char *c_str;

    if (nondet_bool()) {
        c_str = NULL;
    } else {
        /* Assume the length of the string is bounded by some max length */
        __CPROVER_assume(len <= MAX_BUFFER_SIZE);
        ASSUME_VALID_MEMORY_COUNT(c_str, len);

        /* Need *c_str to be a '\0'-terminated C string, so assume an arbitrary character is 0 */
        int index;
        __CPROVER_assume(index >= 0 && index < len);
        c_str[index] = 0;
    }

    /* operation under verification */
    struct aws_byte_buf buf = aws_byte_buf_from_c_str(c_str);

    /* assertions */
    assert(aws_byte_buf_is_valid(&buf));
    assert(buf.allocator == NULL);
    if (buf.buffer) {
        assert(buf.len == strlen(c_str));
        assert(buf.capacity == buf.len);
        assert_bytes_match(buf.buffer, (uint8_t *)c_str, buf.len);
    } else {
        assert(buf.len == 0);
        assert(buf.capacity == 0);
    }
}
