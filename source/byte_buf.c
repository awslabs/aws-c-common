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

bool aws_byte_buf_is_valid(const struct aws_byte_buf *buf) {
    return (buf->len <= buf->capacity) && (buf->allocator != NULL) && AWS_MEM_IS_WRITABLE(buf->buffer, buf->len);
}

bool aws_byte_cursor_is_valid(const struct aws_byte_cursor *cursor) {
    return (cursor->ptr != NULL && cursor->len != 0) && AWS_MEM_IS_WRITABLE(cursor->ptr, cursor->len);
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
    assert(a && b);
    return aws_array_eq(a->buffer, a->len, b->buffer, b->len);
}

bool aws_byte_buf_eq_ignore_case(const struct aws_byte_buf *a, const struct aws_byte_buf *b) {
    assert(a && b);
    return aws_array_eq_ignore_case(a->buffer, a->len, b->buffer, b->len);
}

bool aws_byte_buf_eq_c_str(const struct aws_byte_buf *buf, const char *c_str) {
    assert(buf && c_str);
    return aws_array_eq_c_str(buf->buffer, buf->len, c_str);
}

bool aws_byte_buf_eq_c_str_ignore_case(const struct aws_byte_buf *buf, const char *c_str) {
    assert(buf && c_str);
    return aws_array_eq_c_str_ignore_case(buf->buffer, buf->len, c_str);
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
    assert(a && b);
    return aws_array_eq(a->ptr, a->len, b->ptr, b->len);
}

bool aws_byte_cursor_eq_ignore_case(const struct aws_byte_cursor *a, const struct aws_byte_cursor *b) {
    assert(a && b);
    return aws_array_eq_ignore_case(a->ptr, a->len, b->ptr, b->len);
}

/* Every possible uint8_t value, lowercased */
static const uint8_t s_tolower_table[256] = {
    0,   1,   2,   3,   4,   5,   6,   7,   8,   9,   10,  11,  12,  13,  14,  15,  16,  17,  18,  19,  20,  21,
    22,  23,  24,  25,  26,  27,  28,  29,  30,  31,  32,  33,  34,  35,  36,  37,  38,  39,  40,  41,  42,  43,
    44,  45,  46,  47,  48,  49,  50,  51,  52,  53,  54,  55,  56,  57,  58,  59,  60,  61,  62,  63,  64,  'a',
    'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w',
    'x', 'y', 'z', 91,  92,  93,  94,  95,  96,  'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm',
    'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', 123, 124, 125, 126, 127, 128, 129, 130, 131,
    132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153,
    154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175,
    176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197,
    198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219,
    220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241,
    242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255};

const uint8_t *aws_lookup_table_to_lower_get(void) {
    return s_tolower_table;
}

bool aws_array_eq_ignore_case(const void *array_a, size_t len_a, const void *array_b, size_t len_b) {
    assert(array_a || (len_a == 0));
    assert(array_b || (len_b == 0));

    if (len_a != len_b) {
        return false;
    }

    const uint8_t *bytes_a = array_a;
    const uint8_t *bytes_b = array_b;
    for (size_t i = 0; i < len_a; ++i) {
        if (s_tolower_table[bytes_a[i]] != s_tolower_table[bytes_b[i]]) {
            return false;
        }
    }

    return true;
}

bool aws_array_eq(const void *array_a, size_t len_a, const void *array_b, size_t len_b) {
    assert(array_a || (len_a == 0));
    assert(array_b || (len_b == 0));

    if (len_a != len_b) {
        return false;
    }

    if (len_a == 0) {
        return true;
    }

    return !memcmp(array_a, array_b, len_a);
}

bool aws_array_eq_c_str_ignore_case(const void *array, size_t array_len, const char *c_str) {
    assert(array || (array_len == 0));
    assert(c_str);

    /* Simpler implementation could have been:
     *   return aws_array_eq_ignore_case(array, array_len, c_str, strlen(c_str));
     * but that would have traversed c_str twice.
     * This implementation traverses c_str just once. */

    const uint8_t *array_bytes = array;
    const uint8_t *str_bytes = (const uint8_t *)c_str;

    for (size_t i = 0; i < array_len; ++i) {
        uint8_t s = str_bytes[i];
        if (s == '\0') {
            return false;
        }

        if (s_tolower_table[array_bytes[i]] != s_tolower_table[s]) {
            return false;
        }
    }

    return str_bytes[array_len] == '\0';
}

bool aws_array_eq_c_str(const void *array, size_t array_len, const char *c_str) {
    assert(array || (array_len == 0));
    assert(c_str);

    /* Simpler implementation could have been:
     *   return aws_array_eq(array, array_len, c_str, strlen(c_str));
     * but that would have traversed c_str twice.
     * This implementation traverses c_str just once. */

    const uint8_t *array_bytes = array;
    const uint8_t *str_bytes = (const uint8_t *)c_str;

    for (size_t i = 0; i < array_len; ++i) {
        uint8_t s = str_bytes[i];
        if (s == '\0') {
            return false;
        }

        if (array_bytes[i] != s) {
            return false;
        }
    }

    return str_bytes[array_len] == '\0';
}

uint64_t aws_hash_array_ignore_case(const void *array, size_t len) {
    /* FNV-1a: https://en.wikipedia.org/wiki/Fowler%E2%80%93Noll%E2%80%93Vo_hash_function */
    const uint64_t fnv_offset_basis = 0xcbf29ce484222325ULL;
    const uint64_t fnv_prime = 0x100000001b3ULL;

    const uint8_t *i = array;
    const uint8_t *end = i + len;

    uint64_t hash = fnv_offset_basis;
    while (i != end) {
        const uint8_t lower = s_tolower_table[*i++];
        hash ^= lower;
        hash *= fnv_prime;
    }
    return hash;
}

uint64_t aws_hash_byte_cursor_ptr_ignore_case(const void *item) {
    const struct aws_byte_cursor *cursor = item;
    return aws_hash_array_ignore_case(cursor->ptr, cursor->len);
}

bool aws_byte_cursor_eq_byte_buf(const struct aws_byte_cursor *a, const struct aws_byte_buf *b) {
    assert(a && b);
    return aws_array_eq(a->ptr, a->len, b->buffer, b->len);
}

bool aws_byte_cursor_eq_byte_buf_ignore_case(const struct aws_byte_cursor *a, const struct aws_byte_buf *b) {
    assert(a && b);
    return aws_array_eq_ignore_case(a->ptr, a->len, b->buffer, b->len);
}

bool aws_byte_cursor_eq_c_str(const struct aws_byte_cursor *cursor, const char *c_str) {
    assert(cursor && c_str);
    return aws_array_eq_c_str(cursor->ptr, cursor->len, c_str);
}

bool aws_byte_cursor_eq_c_str_ignore_case(const struct aws_byte_cursor *cursor, const char *c_str) {
    assert(cursor && c_str);
    return aws_array_eq_c_str_ignore_case(cursor->ptr, cursor->len, c_str);
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

int aws_byte_buf_append_with_lookup(
    struct aws_byte_buf *to,
    const struct aws_byte_cursor *from,
    const uint8_t *lookup_table) {
    assert(from->ptr);
    assert(to->buffer);
    AWS_PRECONDITION(aws_byte_buf_is_valid(to));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(from));
    AWS_PRECONDITION(AWS_MEM_IS_READABLE(lookup_table, 256));

    if (to->capacity - to->len < from->len) {
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    for (size_t i = 0; i < from->len; ++i) {
        to->buffer[to->len + i] = lookup_table[from->ptr[i]];
    }

    if (aws_add_size_checked(to->len, from->len, &to->len)) {
        return AWS_OP_ERR;
    }

    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_append_dynamic(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    assert(from->ptr);
    assert(to->buffer);
    AWS_PRECONDITION(aws_byte_buf_is_valid(to));
    AWS_PRECONDITION(aws_byte_cursor_is_valid(from));

    if (to->capacity - to->len < from->len) {
        /*
         * NewCapacity = Max(OldCapacity * 2, OldCapacity + MissingCapacity)
         */
        size_t missing_capacity = from->len - (to->capacity - to->len);

        size_t required_capacity = 0;
        if (aws_add_size_checked(to->capacity, missing_capacity, &required_capacity)) {
            return AWS_OP_ERR;
        }

        /*
         * It's ok if this overflows, just clamp to max possible.
         * In theory this lets us still grow a buffer that's larger than 1/2 size_t space
         * at least enough to accommodate the append.
         */
        size_t growth_capacity = aws_add_size_saturating(to->capacity, to->capacity);

        size_t new_capacity = required_capacity;
        if (new_capacity < growth_capacity) {
            new_capacity = growth_capacity;
        }

        /*
         * Attempt to resize - we intentionally do not use reserve() in order to preserve
         * the (unlikely) use case of from and to being the same buffer range.
         */

        /*
         * Try the max, but if that fails and the required is smaller, try it in fallback
         */
        uint8_t *new_buffer = aws_mem_acquire(to->allocator, new_capacity);
        if (new_buffer == NULL) {
            if (new_capacity > required_capacity) {
                new_capacity = required_capacity;
                new_buffer = aws_mem_acquire(to->allocator, new_capacity);
                if (new_buffer == NULL) {
                    return AWS_OP_ERR;
                }
            } else {
                return AWS_OP_ERR;
            }
        }

        /*
         * Copy old buffer -> new buffer
         */
        memcpy(new_buffer, to->buffer, to->len);

        /*
         * Copy what we actually wanted to append in the first place
         */
        memcpy(new_buffer + to->len, from->ptr, from->len);

        /*
         * Get rid of the old buffer
         */
        aws_mem_release(to->allocator, to->buffer);

        /*
         * Switch to the new buffer
         */
        to->buffer = new_buffer;
        to->capacity = new_capacity;
    } else {
        memcpy(to->buffer + to->len, from->ptr, from->len);
    }

    to->len += from->len;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(to));
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(from));
    return AWS_OP_SUCCESS;
}

int aws_byte_buf_reserve(struct aws_byte_buf *buffer, size_t requested_capacity) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buffer));
    if (requested_capacity <= buffer->capacity) {
        return AWS_OP_SUCCESS;
    }

    if (aws_mem_realloc(buffer->allocator, (void **)&buffer->buffer, buffer->capacity, requested_capacity)) {
        return AWS_OP_ERR;
    }

    buffer->capacity = requested_capacity;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(buffer));
    return AWS_OP_SUCCESS;
}

struct aws_byte_cursor aws_byte_cursor_right_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    struct aws_byte_cursor trimmed = *source;

    while (trimmed.len > 0 && predicate(*(trimmed.ptr + trimmed.len - 1))) {
        --trimmed.len;
    }

    return trimmed;
}

struct aws_byte_cursor aws_byte_cursor_left_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    struct aws_byte_cursor trimmed = *source;

    while (trimmed.len > 0 && predicate(*(trimmed.ptr))) {
        --trimmed.len;
        ++trimmed.ptr;
    }

    return trimmed;
}

struct aws_byte_cursor aws_byte_cursor_trim_pred(
    const struct aws_byte_cursor *source,
    aws_byte_predicate_fn *predicate) {
    struct aws_byte_cursor left_trimmed = aws_byte_cursor_left_trim_pred(source, predicate);
    return aws_byte_cursor_right_trim_pred(&left_trimmed, predicate);
}

bool aws_byte_cursor_satisfies_pred(const struct aws_byte_cursor *source, aws_byte_predicate_fn *predicate) {
    struct aws_byte_cursor trimmed = aws_byte_cursor_left_trim_pred(source, predicate);

    return trimmed.len == 0;
}
