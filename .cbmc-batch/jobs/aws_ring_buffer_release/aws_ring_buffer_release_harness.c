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
#include <aws/common/ring_buffer.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_ring_buffer_release_harness() {
    /* parameters */
    struct aws_ring_buffer ring_buf;
    size_t ring_buf_size;
    struct aws_byte_buf buf;

    /* assumptions */
    ensure_ring_buffer_has_allocated_members(&ring_buf, ring_buf_size);
    ensure_ring_buffer_is_not_empty(&ring_buf);
    __CPROVER_assume(aws_ring_buffer_is_valid(&ring_buf));
    ensure_byte_buf_has_allocated_buffer_member_in_ring_buf(&buf, &ring_buf);
    __CPROVER_assume(aws_byte_buf_is_valid(&buf));

    struct aws_ring_buffer ring_buf_pre = ring_buf;

    aws_ring_buffer_release(&ring_buf, &buf);

    /* assertions */
    assert(aws_ring_buffer_is_valid(&ring_buf));
    assert(aws_atomic_load_ptr(&ring_buf.head) == aws_atomic_load_ptr(&ring_buf_pre.head));
    assert(buf.allocator == NULL);
    assert(buf.buffer == NULL);
    assert(buf.len == 0);
    assert(buf.capacity == 0);
}
