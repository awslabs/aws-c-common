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
#include <aws/common/uuid.h>

#include <aws/common/byte_buf.h>

#include <aws/testing/aws_test_harness.h>

static int s_uuid_string_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct aws_uuid uuid;
    ASSERT_SUCCESS(aws_uuid_init(&uuid));

    uint8_t uuid_array[AWS_UUID_STR_LEN] = {0};
    struct aws_byte_buf uuid_buf = aws_byte_buf_from_array(uuid_array, sizeof(uuid_array));
    uuid_buf.len = 0;

    ASSERT_SUCCESS(aws_uuid_to_str(&uuid, &uuid_buf));
    uint8_t zerod_buf[AWS_UUID_STR_LEN] = {0};
    ASSERT_UINT_EQUALS(AWS_UUID_STR_LEN, uuid_buf.len);
    ASSERT_FALSE(0 == memcmp(zerod_buf, uuid_array, sizeof(uuid_array)));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(uuid_string, s_uuid_string_fn)
