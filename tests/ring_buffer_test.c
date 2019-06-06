/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/testing/aws_test_harness.h>
#include <aws/common/ring_buffer.h>

static int s_test_1_to_1_acquire_release_wraps(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_ring_buffer ring_buffer;
    size_t buf_size = 16;
    ASSERT_SUCCESS(aws_ring_buffer_init(&ring_buffer, allocator, buf_size));

    struct aws_byte_buf vended_buffer;
    AWS_ZERO_STRUCT(vended_buffer);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 4, &vended_buffer));
    uint8_t *ptr = vended_buffer.buffer;
    ASSERT_UINT_EQUALS(4, vended_buffer.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer));
    aws_ring_buffer_release(&ring_buffer, &vended_buffer);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 8, &vended_buffer));
    ASSERT_PTR_EQUALS(ptr + 4, vended_buffer.buffer);
    ASSERT_UINT_EQUALS(8, vended_buffer.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer));
    aws_ring_buffer_release(&ring_buffer, &vended_buffer);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 4, &vended_buffer));
    ASSERT_PTR_EQUALS(ptr + 12, vended_buffer.buffer);
    ASSERT_UINT_EQUALS(4, vended_buffer.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer));
    aws_ring_buffer_release(&ring_buffer, &vended_buffer);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 8, &vended_buffer));
    ASSERT_PTR_EQUALS(ptr, vended_buffer.buffer);
    ASSERT_UINT_EQUALS(8, vended_buffer.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer));
    aws_ring_buffer_release(&ring_buffer, &vended_buffer);

    aws_ring_buffer_clean_up(&ring_buffer);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(ring_buffer_1_to_1_acquire_release_wraps_test, s_test_1_to_1_acquire_release_wraps)

static int s_test_release_after_full(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_ring_buffer ring_buffer;
    size_t buf_size = 16;
    ASSERT_SUCCESS(aws_ring_buffer_init(&ring_buffer, allocator, buf_size));

    struct aws_byte_buf vended_buffer_1;
    AWS_ZERO_STRUCT(vended_buffer_1);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 12, &vended_buffer_1));
    uint8_t *ptr = vended_buffer_1.buffer;
    ASSERT_UINT_EQUALS(12, vended_buffer_1.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_1));

    struct aws_byte_buf vended_buffer_2;
    AWS_ZERO_STRUCT(vended_buffer_2);
    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 4, &vended_buffer_2));
    ASSERT_PTR_EQUALS(ptr + 12, vended_buffer_2.buffer);
    ASSERT_UINT_EQUALS(4, vended_buffer_2.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_2));

    ASSERT_ERROR(AWS_ERROR_NO_AVAILABLE_BUFFERS, aws_ring_buffer_acquire_hard(&ring_buffer, 1, &vended_buffer_1));
    
    aws_ring_buffer_release(&ring_buffer, &vended_buffer_1);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_hard(&ring_buffer, 8, &vended_buffer_2));
    ASSERT_PTR_EQUALS(ptr, vended_buffer_2.buffer);
    ASSERT_UINT_EQUALS(8, vended_buffer_2.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_2));
    aws_ring_buffer_release(&ring_buffer, &vended_buffer_2);

    aws_ring_buffer_clean_up(&ring_buffer);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(ring_buffer_release_after_full_test, s_test_release_after_full)

static int s_test_acquire_soft(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_ring_buffer ring_buffer;
    size_t buf_size = 16;
    ASSERT_SUCCESS(aws_ring_buffer_init(&ring_buffer, allocator, buf_size));

    struct aws_byte_buf vended_buffer_1;
    AWS_ZERO_STRUCT(vended_buffer_1);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 12, &vended_buffer_1));
    uint8_t *ptr = vended_buffer_1.buffer;
    ASSERT_UINT_EQUALS(12, vended_buffer_1.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_1));

    struct aws_byte_buf vended_buffer_2;
    AWS_ZERO_STRUCT(vended_buffer_2);
    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 8, &vended_buffer_2));
    ASSERT_PTR_EQUALS(ptr + 12, vended_buffer_2.buffer);
    ASSERT_UINT_EQUALS(4, vended_buffer_2.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_2));

    ASSERT_ERROR(AWS_ERROR_NO_AVAILABLE_BUFFERS, aws_ring_buffer_acquire_soft(&ring_buffer, 1, &vended_buffer_1));

    aws_ring_buffer_release(&ring_buffer, &vended_buffer_1);
    aws_ring_buffer_release(&ring_buffer, &vended_buffer_2);

    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 8, &vended_buffer_1));
    ASSERT_PTR_EQUALS(ptr, vended_buffer_1.buffer);
    ASSERT_UINT_EQUALS(8, vended_buffer_1.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_1));

    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 8, &vended_buffer_2));
    ASSERT_PTR_EQUALS(ptr + 8, vended_buffer_2.buffer);
    ASSERT_UINT_EQUALS(7, vended_buffer_2.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_2));

    aws_ring_buffer_release(&ring_buffer, &vended_buffer_1);
    aws_ring_buffer_release(&ring_buffer, &vended_buffer_2);

    /* do the same again, making sure we don't have an off by one error in the math. */
    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 8, &vended_buffer_1));
    ASSERT_PTR_EQUALS(ptr, vended_buffer_1.buffer);
    ASSERT_UINT_EQUALS(8, vended_buffer_1.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_1));

    ASSERT_SUCCESS(aws_ring_buffer_acquire_soft(&ring_buffer, 8, &vended_buffer_2));
    ASSERT_PTR_EQUALS(ptr + 8, vended_buffer_2.buffer);
    ASSERT_UINT_EQUALS(7, vended_buffer_2.capacity);
    ASSERT_TRUE(aws_ring_buffer_buf_belongs_to_pool(&ring_buffer, &vended_buffer_2));

    aws_ring_buffer_release(&ring_buffer, &vended_buffer_1);
    aws_ring_buffer_release(&ring_buffer, &vended_buffer_2);

    aws_ring_buffer_clean_up(&ring_buffer);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(ring_buffer_acquire_soft_test, s_test_acquire_soft)