/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_cursor_from_array_harness() {
    /* parameters */
    size_t length;
    uint8_t *array;

    /* assumption */
    ASSUME_VALID_MEMORY_COUNT(array, length);

    /* operation under verification */
    struct aws_byte_cursor cur = aws_byte_cursor_from_array(array, length);

    /* assertions */
    assert(aws_byte_cursor_is_valid(&cur));
    assert(cur.len == length);
    if (cur.ptr) {
        assert_bytes_match(cur.ptr, array, cur.len);
    }
}
