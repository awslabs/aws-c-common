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
#include <proof_helpers/proof_allocators.h>

void aws_byte_buf_init_harness() {
    /* data structure */
    struct aws_byte_buf buf; /* Precondition: buf is non-null */

    /* parameters */
    struct aws_allocator *allocator = can_fail_allocator(); /* Precondition: allocator is non-null */
    size_t capacity;

    if (aws_byte_buf_init(&buf, allocator, capacity) == AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_byte_buf_is_valid(&buf));
        assert(buf.allocator == allocator);
        assert(buf.len == 0);
        assert(buf.capacity == capacity);
    }
}
