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

#include <inttypes.h>
#include <stdio.h>

#define UUID_FORMAT                                                                                                    \
    "%02" SCNx8 "%02" SCNx8 "%02" SCNx8 "%02" SCNx8 "-%02" SCNx8 "%02" SCNx8 "-%02" SCNx8 "%02" SCNx8 "-%02" SCNx8     \
    "%02" SCNx8 "-%02" SCNx8 "%02" SCNx8 "%02" SCNx8 "%02" SCNx8 "%02" SCNx8 "%02" SCNx8

#include <stdio.h>

#ifdef _MSC_VER
/* disables warning non const declared initializers for Microsoft compilers */
#    pragma warning(disable : 4204)
#    pragma warning(disable : 4706)
/* sprintf warning (we already check the bounds in this case). */
#    pragma warning(disable : 4996)
#endif

int aws_uuid_init(struct aws_uuid *uuid) {
    struct aws_byte_buf buf = {
        .buffer = uuid->uuid_data,
        .len = 0,
        .capacity = sizeof(uuid->uuid_data),
        .allocator = NULL,
    };
    return aws_device_random_buffer(&buf);
}

int aws_uuid_init_from_str(struct aws_uuid *uuid, struct aws_byte_cursor *uuid_str) {
    if (uuid_str->len < AWS_UUID_STR_LEN - 1) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    char cpy[AWS_UUID_STR_LEN] = {0};
    memcpy(cpy, uuid_str->ptr, AWS_UUID_STR_LEN - 1);

    AWS_ZERO_STRUCT(*uuid);

    if (16 != sscanf(
                  cpy,
                  UUID_FORMAT,
                  &uuid->uuid_data[0],
                  &uuid->uuid_data[1],
                  &uuid->uuid_data[2],
                  &uuid->uuid_data[3],
                  &uuid->uuid_data[4],
                  &uuid->uuid_data[5],
                  &uuid->uuid_data[6],
                  &uuid->uuid_data[7],
                  &uuid->uuid_data[8],
                  &uuid->uuid_data[9],
                  &uuid->uuid_data[10],
                  &uuid->uuid_data[11],
                  &uuid->uuid_data[12],
                  &uuid->uuid_data[13],
                  &uuid->uuid_data[14],
                  &uuid->uuid_data[15])) {
        return aws_raise_error(AWS_ERROR_MALFORMED_INPUT_STRING);
    }

    return AWS_OP_SUCCESS;
}

int aws_uuid_to_str(struct aws_uuid *uuid, struct aws_byte_buf *output) {
    if (output->capacity - output->len < AWS_UUID_STR_LEN) {
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    sprintf(
        (char *)(output->buffer + output->len),
        UUID_FORMAT,
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
        uuid->uuid_data[15]);

    output->len += AWS_UUID_STR_LEN - 1;

    return AWS_OP_SUCCESS;
}
