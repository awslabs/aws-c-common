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

    size_t current_pos = 0;
    size_t last_offset = 0;

    for(; current_pos < input_str->len; ++current_pos) {
        if(current_pos < input_str->len - 2 && input_str->buffer[current_pos] == (uint8_t)split_on) {
            struct aws_byte_buf buffer = {
                    .buffer = input_str->buffer + last_offset,
                    .len = current_pos - last_offset,
            };

            if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
                return AWS_OP_ERR;
            }

            last_offset = current_pos + 1;
        }
    }

    if (last_offset < input_str->len) {
        struct aws_byte_buf buffer = {
                .buffer = input_str->buffer + last_offset,
                .len = current_pos - last_offset,
        };

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}

int aws_string_split_on_str(struct aws_byte_buf *input_str, char *split_on,
                            struct aws_array_list *output) {
    assert(input_str);
    assert(output);
    assert(output->item_size >= sizeof(struct aws_byte_buf));
    assert(split_on);
    size_t token_len = strlen(split_on);
    assert(token_len);

    size_t current_pos = 0;
    size_t last_offset = 0;

    int8_t possible_match_idx = 0;

    for(; current_pos < input_str->len; ++current_pos) {

        if (current_pos < input_str->len - 2 && input_str->buffer[current_pos] == (uint8_t)split_on[possible_match_idx]) {

            possible_match_idx += 1;
            if (possible_match_idx == token_len) {

                struct aws_byte_buf buffer = {
                        .buffer = input_str->buffer + last_offset,
                        /* we read the entire token so that needs to be accounted for. */
                        .len = current_pos - last_offset - (token_len - 1),
                };

                if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
                    return AWS_OP_ERR;
                }

                last_offset = current_pos + 1;
                possible_match_idx = 0;
            }
        }
        else {
            possible_match_idx = 0;
        }
    }

    /* in this case we're only here if we didn't read the entire split token so we don't account for the token length */
    if (last_offset < input_str->len) {
        struct aws_byte_buf buffer = {
                .buffer = input_str->buffer + last_offset,
                .len = current_pos - last_offset,
        };

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&buffer))) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}
