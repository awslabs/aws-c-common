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
#include <aws/common/device_random.h>
#include <stdio.h>

int aws_uuid_init(struct aws_uuid *uuid) {
    struct aws_byte_buf buf = {
            .buffer = uuid->uuid_data,
            .len = 0,
            .capacity = sizeof(uuid->uuid_data),
            .allocator = NULL,
    };
    return aws_device_random_buffer(&buf);
}

int aws_uuid_to_str(struct aws_uuid *uuid, struct aws_byte_buf *output) {
    if (output->capacity - output->len < AWS_UUID_STR_LEN) {
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    sprintf((char *)(output->buffer + output->len),
            "%02x%02x%02x%02x-%02x%02x-%02x%02x-%02x%02x-%02x%02x%02x%02x%02x%02x",
            uuid->uuid_data[0],
            uuid->uuid_data[1],
            uuid->uuid_data[2],
            uuid->uuid_data[3],
            uuid->uuid_data[4],
            uuid->uuid_data[5],
            uuid->uuid_data[6],
            uuid->uuid_data[7],
            uuid->uuid_data[8],
            uuid->uuid_data[9],
            uuid->uuid_data[10],
            uuid->uuid_data[11],
            uuid->uuid_data[12],
            uuid->uuid_data[13],
            uuid->uuid_data[14],
            uuid->uuid_data[15]
    );

    output->len += AWS_UUID_STR_LEN;

    return AWS_OP_SUCCESS;
}
