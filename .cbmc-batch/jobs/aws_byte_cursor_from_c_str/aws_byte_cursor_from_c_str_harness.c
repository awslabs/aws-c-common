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

void aws_byte_cursor_from_c_str_harness() {
    /* parameters */
    const char *c_str = nondet_bool() ? NULL : ensure_c_str_is_allocated(MAX_BUFFER_SIZE);

    /* operation under verification */
    struct aws_byte_cursor cur = aws_byte_cursor_from_c_str(c_str);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    if (cur.ptr) { /* if ptr is NULL len shoud be 0, otherwise equal to c_str */
        assert(cur.len == strlen(c_str));
        assert_bytes_match(cur.ptr, (uint8_t *)c_str, cur.len);
    } else {
        assert(cur.len == 0);
    }
}
