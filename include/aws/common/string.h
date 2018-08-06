#ifndef AWS_COMMON_STRING_H
#define AWS_COMMON_STRING_H
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
#include <aws/common/common.h>

/**
 * Represents an immutable string holding either text or binary data. If the
 * string is in constant memory or memory that should otherwise not be freed by
 * this struct, set allocator to NULL and destroy function will be a no-op.
 *
 * This is for use cases where the entire struct and the data bytes themselves
 * need to be held in dynamic memory, such as when held by a struct
 * aws_hash_table. The data bytes themselves are always held in contiguous
 * memory immediately after the end of the struct aws_string, and the memory for
 * both the header and the data bytes is allocated together.
 *
 * Use the aws_string_bytes function to access the data bytes. A null byte is
 * always included immediately after the data but not counted in the length, so
 * that the output of aws_string_bytes can be treated as a C-string in cases
 * where none of the the data bytes are null.
 */
struct aws_string {
    struct aws_allocator *allocator;
    size_t len;
};

static inline const uint8_t *aws_string_bytes(const struct aws_string *hdr) {
    return (const uint8_t *)(hdr + 1);
}

/**
 * Returns true if bytes of string and cursor are the same, false otherwise.
 */
static inline bool aws_string_eq_byte_cursor(const struct aws_string *str, const struct aws_byte_cursor *cur) {
    if (str->len != cur->len) {
        return false;
    }
    return (!memcmp(aws_string_bytes(str), cur->ptr, cur->len));
}

/**
 * Returns true if bytes of string and buffer are the same, false otherwise.
 */
static inline bool aws_string_eq_byte_buf(const struct aws_string *str, const struct aws_byte_buf *buf) {
    if (str->len != buf->len) {
        return false;
    }
    return (!memcmp(aws_string_bytes(str), buf->buffer, buf->len));
}

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Constructor functions which copy data from null-terminated C-string or array of unsigned or signed characters.
 */
AWS_COMMON_API
const struct aws_string *aws_string_new_from_c_str(struct aws_allocator *allocator, const char *c_str);
AWS_COMMON_API
const struct aws_string *aws_string_new_from_array(struct aws_allocator *allocator, const uint8_t *bytes, size_t len);

/**
 * Deallocate string. Takes a (void *) so it can be used as a destructor function for struct aws_hash_table.
 */
AWS_COMMON_API
void aws_string_destroy(void *str);

/**
 * Zeroes out the data bytes of string and then deallocates the memory.
 * Not safe to run on a string created with AWS_STATIC_STRING_FROM_LITERAL.
 */
AWS_COMMON_API
void aws_string_destroy_secure(void *str);

/**
 * Compares lexicographical ordering of two strings. This is a binary
 * byte-by-byte comparison, treating bytes as unsigned integers. It is suitable
 * for either textual or binary data and is unaware of unicode or any other byte
 * encoding. If both strings are identical in the bytes of the shorter string,
 * then the longer string is lexicographically after the shorter.
 *
 * Returns a positive number if string a > string b. (i.e., string a is
 * lexicographically after string b.) Returns zero if string a = string b.
 * Returns negative number if string a < string b.
 */
AWS_COMMON_API
int aws_string_compare(const struct aws_string *a, const struct aws_string *b);

/**
 * A convenience function for sorting lists of (const struct aws_string *) elements. This can be used as a
 * comparator for aws_array_list_sort. It is just a simple wrapper around aws_string_compare.
 */
AWS_COMMON_API
int aws_array_list_comparator_string(const void *a, const void *b);

#ifdef __cplusplus
}
#endif

/**
 * Defines a (static const struct aws_string *) with name specified in first
 * argument that points to constant memory and has data bytes containing the
 * string literal in the second argument.
 */
#define AWS_STATIC_STRING_FROM_LITERAL(name, literal)                                                                  \
    static const struct {                                                                                              \
        struct aws_string hdr;                                                                                         \
        uint8_t data[sizeof(literal)];                                                                                 \
    } name##_s = {{NULL, sizeof(literal) - 1}, {literal}};                                                             \
    static const struct aws_string *(name) = &name##_s.hdr

/**
 * Copies all bytes from string to cursor.
 *
 * On success, returns true and updates the cursor pointer/length
 * accordingly. If there is insufficient space in the cursor, returns
 * false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_from_whole_string(
    struct aws_byte_cursor *AWS_RESTRICT cur,
    const struct aws_string *AWS_RESTRICT src) {
    return aws_byte_cursor_write(cur, aws_string_bytes(src), src->len);
}

#endif /* AWS_COMMON_STRING_H */
