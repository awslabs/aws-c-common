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
#include <stdarg.h>

#ifdef _MSC_VER
/* disables warning non const declared initializers for Microsoft compilers */
#    pragma warning(disable : 4204)
#    pragma warning(disable : 4706)
#endif

int aws_byte_buf_init(
    struct aws_allocator *allocator,
    struct aws_byte_buf *buf,
    size_t len) {
    buf->buffer = (uint8_t *)aws_mem_acquire(allocator, len);
    if (!buf->buffer) {
        return AWS_OP_ERR;
    }
    buf->len = 0;
    buf->capacity = len;
    buf->allocator = allocator;
    return AWS_OP_SUCCESS;
}

void aws_byte_buf_clean_up(struct aws_byte_buf *buf) {
    if (buf->allocator && buf->buffer) {
        aws_mem_release(buf->allocator, (void *)buf->buffer);
    }
    buf->allocator = NULL;
    buf->buffer = NULL;
    buf->len = 0;
    buf->capacity = 0;
}

int aws_byte_buf_split_on_char_n(
    struct aws_byte_buf *input_str,
    char split_on,
    struct aws_array_list *output,
    size_t n) {
    assert(input_str);
    assert(output);
    assert(output->item_size >= sizeof(struct aws_byte_cursor));

    size_t max_splits = n > 0 ? n : SIZE_MAX;
    size_t last_offset = 0, split_count = 0;
    uint8_t *new_location = NULL;

    struct aws_byte_cursor current_pos = aws_byte_cursor_from_buf(input_str);

    while (split_count < max_splits
           && (new_location =
                   memchr(current_pos.ptr, split_on, current_pos.len))) {

        size_t distance_from_origin = new_location - current_pos.ptr;

        struct aws_byte_cursor buffer =
            aws_byte_cursor_advance(&current_pos, distance_from_origin);
        /* skip ahead by one to jump over the split_on character.*/
        aws_byte_cursor_advance(&current_pos, 1);

        if (AWS_UNLIKELY(
                aws_array_list_push_back(output, (const void *)&buffer))) {
            return AWS_OP_ERR;
        }

        last_offset = distance_from_origin + 1;
        split_count += 1;
    }

    if (last_offset < input_str->len) {
        return aws_array_list_push_back(output, (const void *)&current_pos);
    }

    /* if we get here, we hit the end and we need to add an empty split */
    struct aws_byte_cursor cursor = aws_byte_cursor_from_array(NULL, 0);

    if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&cursor))) {
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

int aws_byte_buf_split_on_char(
    struct aws_byte_buf *input_str,
    char split_on,
    struct aws_array_list *output) {
    return aws_byte_buf_split_on_char_n(input_str, split_on, output, 0);
}

int aws_byte_buf_cat(struct aws_byte_buf *dest, size_t number_of_args, ...) {
    assert(dest);
    assert(number_of_args > 1);

    va_list ap;
    va_start(ap, number_of_args);

    for (size_t i = 0; i < number_of_args; ++i) {
        struct aws_byte_buf *buffer = va_arg(ap, struct aws_byte_buf *);
        struct aws_byte_cursor cursor = aws_byte_cursor_from_buf(buffer);

        if (aws_byte_buf_append(dest, &cursor)) {
            va_end(ap);
            return AWS_OP_ERR;
        }
    }

    va_end(ap);
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_append(struct aws_byte_buf *to, struct aws_byte_cursor *from) {
    assert(from->ptr);
    assert(to->buffer);

    if (to->capacity - to->len < from->len) {
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    memcpy(to->buffer + to->len, from->ptr, from->len);
    to->len += from->len;
    return AWS_OP_SUCCESS;
}
