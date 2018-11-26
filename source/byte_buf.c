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

int aws_byte_buf_init(struct aws_byte_buf *buf, struct aws_allocator *allocator, size_t capacity) {
    buf->buffer = (uint8_t *)aws_mem_acquire(allocator, capacity);
    if (!buf->buffer) {
        return AWS_OP_ERR;
    }
    buf->len = 0;
    buf->capacity = capacity;
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

void aws_byte_buf_secure_zero(struct aws_byte_buf *buf) {
    if (buf->buffer) {
        aws_secure_zero(buf->buffer, buf->capacity);
    }
    buf->len = 0;
}

void aws_byte_buf_clean_up_secure(struct aws_byte_buf *buf) {
    aws_byte_buf_secure_zero(buf);
    aws_byte_buf_clean_up(buf);
}

bool aws_byte_buf_eq(const struct aws_byte_buf *a, const struct aws_byte_buf *b) {
    if (!a || !b) {
        return (a == b);
    }

    if (a->len != b->len) {
        return false;
    }

    if (!a->buffer || !b->buffer) {
        return (a->buffer == b->buffer);
    }

    return !memcmp(a->buffer, b->buffer, a->len);
}

int aws_byte_buf_init_copy_from_cursor(
    struct aws_byte_buf *dest,
    struct aws_allocator *allocator,
    struct aws_byte_cursor src) {
    assert(allocator);
    assert(dest);

    dest->len = 0;
    dest->capacity = 0;
    dest->allocator = NULL;
    if (src.ptr == NULL) {
        dest->buffer = NULL;
        return AWS_OP_SUCCESS;
    }

    dest->buffer = (uint8_t *)aws_mem_acquire(allocator, sizeof(uint8_t) * src.len);
    if (dest->buffer == NULL) {
        return AWS_OP_ERR;
    }

    dest->len = src.len;
    dest->capacity = src.len;
    dest->allocator = allocator;
    memcpy(dest->buffer, src.ptr, src.len);
    return AWS_OP_SUCCESS;
}

bool aws_byte_cursor_next_split(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    struct aws_byte_cursor *AWS_RESTRICT substr) {

    bool first_run = false;
    if (!substr->ptr) {
        first_run = true;
        substr->ptr = input_str->ptr;
        substr->len = 0;
    }

    if (substr->ptr > input_str->ptr + input_str->len) {
        /* This will hit if the last substring returned was an empty string after terminating split_on. */
        AWS_ZERO_STRUCT(*substr);
        return false;
    }

    /* Calculate first byte to search. */
    substr->ptr += substr->len;
    /* Remaining bytes is the number we started with minus the number of bytes already read. */
    substr->len = input_str->len - (substr->ptr - input_str->ptr);

    if (!first_run && substr->len == 0) {
        /* This will hit if the string doesn't end with split_on but we're done. */
        AWS_ZERO_STRUCT(*substr);
        return false;
    }

    if (!first_run && *substr->ptr == split_on) {
        /* If not first rodeo and the character after substr is split_on, skip. */
        ++substr->ptr;
        --substr->len;

        if (substr->len == 0) {
            /* If split character was last in the string, return empty substr. */
            return true;
        }
    }

    uint8_t *new_location = memchr(substr->ptr, split_on, substr->len);
    if (new_location) {

        /* Character found, update string length. */
        substr->len = new_location - substr->ptr;
    }

    return true;
}

int aws_byte_cursor_split_on_char_n(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    size_t n,
    struct aws_array_list *AWS_RESTRICT output) {
    assert(input_str && input_str->ptr);
    assert(output);
    assert(output->item_size >= sizeof(struct aws_byte_cursor));

    size_t max_splits = n > 0 ? n : SIZE_MAX;
    size_t split_count = 0;

    struct aws_byte_cursor substr;
    AWS_ZERO_STRUCT(substr);

    /* Until we run out of substrs or hit the max split count, keep iterating and pushing into the array list. */
    while (split_count <= max_splits && aws_byte_cursor_next_split(input_str, split_on, &substr)) {

        if (split_count == max_splits) {
            /* If this is the last split, take the rest of the string. */
            substr.len = input_str->len - (substr.ptr - input_str->ptr);
        }

        if (AWS_UNLIKELY(aws_array_list_push_back(output, (const void *)&substr))) {
            return AWS_OP_ERR;
        }
        ++split_count;
    }

    return AWS_OP_SUCCESS;
}

int aws_byte_cursor_split_on_char(
    const struct aws_byte_cursor *AWS_RESTRICT input_str,
    char split_on,
    struct aws_array_list *AWS_RESTRICT output) {

    return aws_byte_cursor_split_on_char_n(input_str, split_on, 0, output);
}

int aws_byte_buf_cat(struct aws_byte_buf *dest, size_t number_of_args, ...) {
    assert(dest);

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

bool aws_byte_cursor_eq(const struct aws_byte_cursor *a, const struct aws_byte_cursor *b) {

    if (!a || !b) {
        return (a == b);
    }

    if (a->len != b->len) {
        return false;
    }

    if (!a->ptr || !b->ptr) {
        return (a->ptr == b->ptr);
    }

    return !memcmp(a->ptr, b->ptr, a->len);
}

bool aws_byte_cursor_eq_byte_buf(const struct aws_byte_cursor *a, const struct aws_byte_buf *b) {

    if (!a || !b) {
        return ((void *)a == (void *)b);
    }

    if (a->len != b->len) {
        return false;
    }

    if (!a->ptr || !b->buffer) {
        return (a->ptr == b->buffer);
    }

    return !memcmp(a->ptr, b->buffer, a->len);
}

int aws_byte_buf_append(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    assert(from->ptr);
    assert(to->buffer);

    if (to->capacity - to->len < from->len) {
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    memcpy(to->buffer + to->len, from->ptr, from->len);
    to->len += from->len;
    return AWS_OP_SUCCESS;
}
