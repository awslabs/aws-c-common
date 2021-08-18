/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_init_harness() {
    /* data structure */
    struct aws_byte_buf buf; /* Precondition: buf is non-null */

    /* parameters */
    struct aws_allocator *allocator = aws_default_allocator(); /* Precondition: allocator is non-null */
    size_t capacity;

    if (aws_byte_buf_init(&buf, allocator, capacity) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_byte_buf_is_valid(&buf));
        assert(buf.allocator == allocator);
        assert(buf.len == 0);
        assert(buf.capacity == capacity);
    }
}
