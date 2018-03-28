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

#include <aws/common/byte_buf.h>
#include <assert.h>

int aws_string_split_on_char(struct aws_byte_buf *input_str, char split_on, struct aws_array_list *output) {
    assert(input_str);
    assert(output);
    assert(output->item_size >= sizeof(struct aws_byte_buf));

    size_t last_offset = 0;
    uint8_t *new_location = NULL;

    while ((new_location = memchr(input_str->buffer + last_offset, split_on, input_str->len - last_offset))) {

        size_t distance_from_origin = new_location - input_str->buffer;

        struct aws_byte_buf buffer = {
                .buffer = input_str->buffer + last_offset,
                .len = distance_from_origin - last_offset,
        };

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
            return AWS_OP_ERR;
        }

        last_offset = distance_from_origin + 1;
    }

    if (last_offset < input_str->len) {
        struct aws_byte_buf buffer = {
            .buffer = input_str->buffer + last_offset,
            .len = input_str->len - last_offset,
        };

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}
