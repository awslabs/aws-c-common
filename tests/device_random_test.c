/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <aws/common/device_random.h>

#include <aws/common/byte_buf.h>

#include <aws/testing/aws_test_harness.h>

static int s_device_rand_u64_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t last_value = 0;

    for (size_t i = 0; i < 100000; ++i) {
        uint64_t next_value = 0;
        ASSERT_SUCCESS(aws_device_random_u64(&next_value));
        ASSERT_FALSE(next_value == last_value);
        ASSERT_TRUE(next_value != 0);
        last_value = next_value;
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(device_rand_u64, s_device_rand_u64_fn)

static int s_device_rand_u32_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint32_t last_value = 0;

    for (size_t i = 0; i < 100000; ++i) {
        uint32_t next_value = 0;
        ASSERT_SUCCESS(aws_device_random_u32(&next_value));

        ASSERT_FALSE(next_value == last_value);
        ASSERT_TRUE(next_value != 0);

        last_value = next_value;
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(device_rand_u32, s_device_rand_u32_fn)

static int s_device_rand_u16_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    uint64_t last_value = 0;

    for (size_t i = 0; i < 100; ++i) {
        uint16_t next_value = 0;
        ASSERT_SUCCESS(aws_device_random_u16(&next_value));

        ASSERT_FALSE(next_value == last_value);
        ASSERT_TRUE(next_value != 0);

        last_value = next_value;
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(device_rand_u16, s_device_rand_u16_fn)

static int s_device_rand_buffer_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    /* why 23? 2 uint64, 1 uint32, 1 uint16, 1 byte left, make sure the leftovers are processed and every branch hit*/
    uint8_t last_value[23] = {0};

    for (size_t i = 0; i < 100000; ++i) {
        uint8_t next_value[23] = {0};
        struct aws_byte_buf buf = aws_byte_buf_from_array(next_value, sizeof(next_value));
        buf.len = 0;

        ASSERT_SUCCESS(aws_device_random_buffer(&buf));
        ASSERT_UINT_EQUALS(buf.capacity, buf.len);
        ASSERT_FALSE(0 == memcmp(last_value, next_value, sizeof(next_value)));

        uint8_t zerod_buf[23] = {0};
        ASSERT_FALSE(0 == memcmp(zerod_buf, next_value, sizeof(next_value)));

        memcpy(last_value, next_value, sizeof(next_value));
    }

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(device_rand_buffer, s_device_rand_buffer_fn)
