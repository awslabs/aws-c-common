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

#include <aws/common/resource_name.h>

#define ARN_DELIMETER ":"

static int s_parse_resource_name_part(
    struct aws_byte_cursor *token_cursor,
    const struct aws_byte_cursor *cursor_split_on,
    struct aws_byte_cursor *prev_token_cursor) {
    *prev_token_cursor = *token_cursor;
    aws_byte_cursor_advance(prev_token_cursor, 1);

    if (aws_byte_cursor_find_exact(prev_token_cursor, cursor_split_on, token_cursor)) {
        return aws_raise_error(AWS_ERROR_MALFORMED_INPUT_STRING);
    }
    prev_token_cursor->len = token_cursor->ptr - prev_token_cursor->ptr;
    return AWS_OP_SUCCESS;
}

AWS_COMMON_API
int aws_resource_name_init_from_cur(struct aws_resource_name *arn, const struct aws_byte_cursor *input) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(input));
    AWS_PRECONDITION(input->ptr);
    AWS_PRECONDITION(arn);

    const struct aws_byte_cursor cursor_split_on = AWS_BYTE_CUR_INIT_FROM_STRING_LITERAL(ARN_DELIMETER);
    struct aws_byte_cursor cursor;

    if (input->len < 4) {
        return aws_raise_error(AWS_ERROR_MALFORMED_INPUT_STRING);
    }
    cursor.ptr = input->ptr;
    cursor.len = 4;
    if (!aws_byte_cursor_eq_c_str(&cursor, "arn:")) {
        return aws_raise_error(AWS_ERROR_MALFORMED_INPUT_STRING);
    }
    cursor.len = input->len;
    aws_byte_cursor_advance(&cursor, 3);

    if (s_parse_resource_name_part(&cursor, &cursor_split_on, &arn->partition)) {
        return aws_raise_error(aws_last_error());
    }

    if (s_parse_resource_name_part(&cursor, &cursor_split_on, &arn->service)) {
        return aws_raise_error(aws_last_error());
    }

    if (s_parse_resource_name_part(&cursor, &cursor_split_on, &arn->region)) {
        return aws_raise_error(aws_last_error());
    }

    if (s_parse_resource_name_part(&cursor, &cursor_split_on, &arn->account_id)) {
        return aws_raise_error(aws_last_error());
    }

    arn->resource_id.ptr = cursor.ptr + 1;
    arn->resource_id.len =
        input->len - 8 - (arn->partition.len + arn->service.len + arn->region.len + arn->account_id.len);

    return AWS_OP_SUCCESS;
}

AWS_COMMON_API
int aws_resource_name_length(const struct aws_resource_name *arn, size_t *size) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->partition));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->service));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->region));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->account_id));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->resource_id));

    *size = arn->partition.len + arn->region.len + arn->service.len + arn->account_id.len + arn->resource_id.len + 8;

    return AWS_OP_SUCCESS;
}

AWS_COMMON_API
int aws_byte_buf_append_resource_name(struct aws_byte_buf *buf, const struct aws_resource_name *arn) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->partition));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->service));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->region));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->account_id));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&arn->resource_id));

    const struct aws_byte_cursor prefix = AWS_BYTE_CUR_INIT_FROM_STRING_LITERAL("arn:");
    const struct aws_byte_cursor colon_cur = AWS_BYTE_CUR_INIT_FROM_STRING_LITERAL(ARN_DELIMETER);

    if (aws_byte_buf_append(buf, &prefix)) {
        return aws_raise_error(aws_last_error());
    }
    if (aws_byte_buf_append(buf, &arn->partition)) {
        return aws_raise_error(aws_last_error());
    }
    if (aws_byte_buf_append(buf, &colon_cur)) {
        return aws_raise_error(aws_last_error());
    }

    if (aws_byte_buf_append(buf, &arn->service)) {
        return aws_raise_error(aws_last_error());
    }
    if (aws_byte_buf_append(buf, &colon_cur)) {
        return aws_raise_error(aws_last_error());
    }

    if (aws_byte_buf_append(buf, &arn->region)) {
        return aws_raise_error(aws_last_error());
    }
    if (aws_byte_buf_append(buf, &colon_cur)) {
        return aws_raise_error(aws_last_error());
    }

    if (aws_byte_buf_append(buf, &arn->account_id)) {
        return aws_raise_error(aws_last_error());
    }
    if (aws_byte_buf_append(buf, &colon_cur)) {
        return aws_raise_error(aws_last_error());
    }

    if (aws_byte_buf_append(buf, &arn->resource_id)) {
        return aws_raise_error(aws_last_error());
    }

    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return AWS_OP_SUCCESS;
}
