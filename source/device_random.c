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

int aws_device_random_u64(uint64_t *output) {
    struct aws_byte_buf buf = {
        .buffer = (uint8_t *)output,
        .len = 0,
        .capacity = sizeof(uint64_t),
        .allocator = NULL,
    };

    return aws_device_random_buffer(&buf);
}

int aws_device_random_u32(uint32_t *output) {
    struct aws_byte_buf buf = {
        .buffer = (uint8_t *)output,
        .len = 0,
        .capacity = sizeof(uint32_t),
        .allocator = NULL,
    };

    return aws_device_random_buffer(&buf);
}

int aws_device_random_u16(uint16_t *output) {
    struct aws_byte_buf buf = {
        .buffer = (uint8_t *)output,
        .len = 0,
        .capacity = sizeof(uint16_t),
        .allocator = NULL,
    };

    return aws_device_random_buffer(&buf);
}

int aws_device_random_u8(uint8_t *output) {
    struct aws_byte_buf buf = {
        .buffer = (uint8_t *)output,
        .len = 0,
        .capacity = sizeof(uint8_t),
        .allocator = NULL,
    };

    return aws_device_random_buffer(&buf);
}
