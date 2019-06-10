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

#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_ring_buffer_init_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    struct aws_allocator *allocator = can_fail_allocator();
    size_t size;

    if (aws_ring_buffer_init(nondet_bool() ? &ring_buf : NULL, nondet_bool() ? allocator : NULL, size) ==
        AWS_OP_SUCCESS) {
        /* assertions */
        assert(aws_ring_buffer_is_valid(&ring_buf));
        assert(ring_buf.allocator == allocator);
        assert(ring_buf.allocation_end - ring_buf.allocation == size);
    }
}
