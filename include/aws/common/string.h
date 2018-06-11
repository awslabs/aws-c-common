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
#include <aws/common/common.h>
#include <aws/common/byte_buf.h>
#include <string.h>

/**
 * Represents an immutable string holding either text or binary data. If the string is in constant
 * memory or memory that should otherwise not be freed by this struct, set allocator to NULL
 * and destroy function will be a no-op.
 *
 * This is for use cases where the entire struct and the data bytes themselves need to be
 * held in dynamic memory, such as when held by a struct aws_hash_table. The data bytes
 * themselves are always held in contiguous memory immediately after the end of the
 * struct aws_string, and the memory for both the header and the data bytes
 * is allocated together.
 *
 * Use the aws_string_bytes function to access the data bytes.
 */
struct aws_string {
    struct aws_allocator * allocator;
    size_t len;
};

static inline const uint8_t * aws_string_bytes(const struct aws_string * hdr) {
    return (const uint8_t *)(hdr + 1);
}

static inline const struct aws_string * aws_string_from_literal_new(struct aws_allocator * allocator, const char * literal) {
    size_t len = strlen(literal);
    struct aws_string * hdr = aws_mem_acquire(allocator, sizeof(struct aws_string) + len);
    if (!hdr) {aws_raise_error(AWS_ERROR_OOM); return NULL;}
    hdr->allocator = allocator;
    hdr->len = len;
    memcpy((void *)aws_string_bytes(hdr), literal, len);
    return hdr;
}

static inline const struct aws_string * aws_string_from_array_new(struct aws_allocator * allocator, const uint8_t * bytes, size_t len) {
    struct aws_string * hdr = aws_mem_acquire(allocator, sizeof(struct aws_string) + len);
    if (!hdr) {aws_raise_error(AWS_ERROR_OOM); return NULL;}
    hdr->allocator = allocator;
    hdr->len = len;
    memcpy((void *)aws_string_bytes(hdr), bytes, len);
    return hdr;
}

static inline const struct aws_string * aws_string_from_c_str_new(struct aws_allocator * allocator, const char * bytes, size_t len) {
    struct aws_string * hdr = aws_mem_acquire(allocator, sizeof(struct aws_string) + len);
    if (!hdr) {aws_raise_error(AWS_ERROR_OOM); return NULL;}
    hdr->allocator = allocator;
    hdr->len = len;
    memcpy((void *)aws_string_bytes(hdr), bytes, len);
    return hdr;
}

/* Takes a void * so it can be used as a destructor function for struct aws_hash_table.
 * That is also why it is not inlined.
 */
void aws_string_destroy(void * buf);

/**
 * Defines a (static const struct aws_string *) with name specified in first argument
 * that points to constant memory and has data bytes containing the string literal in the second argument.
 */
#define AWS_STATIC_STRING_FROM_LITERAL(name, literal)                              \
    static const struct {struct aws_string hdr; uint8_t data[sizeof(literal)-1];}  \
        _ ## name ## _s = {                                                        \
        {NULL,                                                                     \
         sizeof(literal) - 1},                                                     \
        {literal}                                                                  \
    };                                                                             \
    static const struct aws_string * name = & _ ## name ## _s.hdr

/**
 * Copies all bytes from string to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_from_whole_string(struct aws_byte_cursor * AWS_RESTRICT cur, const struct aws_string * AWS_RESTRICT src) {
    return aws_byte_cursor_write(cur, aws_string_bytes(src), src->len);
}


#endif /* AWS_COMMON_STRING_H */
