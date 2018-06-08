#ifndef AWS_COMMON_BYTE_BUF_H
#define AWS_COMMON_BYTE_BUF_H
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
#include <aws/common/array_list.h>
#include <aws/common/byte_order.h>

#include <string.h>
#include <stdint.h>
#include <stdbool.h>

/**
 * Represents a length-delimited binary string or buffer. If byte buffer points to constant
 * memory or memory that should otherwise not be freed by this struct, set allocator to NULL
 * and free function will be a no-op.
 *
 * Note that this structure allocates memory at the buffer pointer only. The struct itself
 * does not get dynamically allocated and must be either maintained or copied to avoid losing
 * access to the memory.
 */
struct aws_byte_buf {
    struct aws_allocator * allocator;
    uint8_t *buffer;
    size_t len;
    size_t capacity;
};

/**
 * Represents an immutable string holding either text or binary data. If the string is in constant
 * memory or memory that should otherwise not be freed by this struct, set allocator to NULL
 * and destroy function will be a no-op.
 *
 * This is for use cases where the entire struct and the data bytes themselves need to be
 * held in dynamic memory, such as when held by a struct aws_hash_table. The data bytes
 * themselves are always held in contiguous memory immediately after the end of the
 * struct aws_string, and the memory for both the header and the data bytes
 * is allocated together. (So we cannot have arrays of strings!)
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

/**
 * Defines a (static const struct aws_string *) with name specified in first argument
 * that points to constant memory and has data bytes containing the string literal in the second argument.
 */
#define AWS_STATIC_STRING_FROM_LITERAL(name, literal)                              \
    static const struct { struct aws_string hdr; uint8_t data[strlen(literal)]; }  \
        _ ## name ## _s = {                                                        \
            {NULL,                                                                 \
             strlen(literal)},                                                     \
            {literal}                                                              \
            };                                                                     \
static const struct aws_string * name = & _ ## name ## _s.hdr


/* Takes a void * so it can be used as a destructor function for struct aws_hash_table.
 * That is also why it is not inlined.
 */
void aws_string_destroy(void * buf);

/**
 * Represents a movable pointer within a larger binary string or buffer.
 */
struct aws_byte_cursor {
    uint8_t *ptr;
    size_t len;
};

#ifdef __cplusplus
extern "C" {
#endif

/**
 * No copies, no string allocations. Fills in output with a list of aws_byte_cursor instances where buffer is
 * an offset into the input_str and len is the length of that string in the original buffer.
 *
 * Edge case rules are as follows:
 * if the string begins with split_on, an empty string will be the first entry in output
 * if the input string has two adjacent split_on tokens, an empty string will be inserted into the output.
 * if the input string ends with split_on, an empty string will be appended to the output.
 *
 * It is the user's responsibility to properly initialize output. Recommended number of preallocated elements from output
 * is your most likely guess for the upper bound of the number of elements resulting from the split.
 *
 * The type that will be stored in output is struct aws_byte_cursor (you'll need this for the item size param).
 *
 * It is the user's responsibility to make sure the input buffer stays in memory long enough to use the results.
 */
AWS_COMMON_API int aws_byte_buf_split_on_char(struct aws_byte_buf *input_str, char split_on,
                                              struct aws_array_list *output);

/**
* No copies, no string allocations. Fills in output with a list of aws_byte_cursor instances where buffer is
* an offset into the input_str and len is the length of that string in the original buffer. N is the max number of splits,
* if this value is zero, it will add all splits to the output.
*
* Edge case rules are as follows:
* if the string begins with split_on, an empty string will be the first entry in output
* if the input string has two adjacent split_on tokens, an empty string will be inserted into the output.
* if the input string ends with split_on, an empty string will be appended to the output.
*
* It is the user's responsibility to properly initialize output. Recommended number of preallocated elements from output
* is your most likely guess for the upper bound of the number of elements resulting from the split.
*
* The type that will be stored in output is struct aws_byte_cursor (you'll need this for the item size param).
*
* It is the user's responsibility to make sure the input buffer stays in memory long enough to use the results.
*/
AWS_COMMON_API int aws_byte_buf_split_on_char_n(struct aws_byte_buf *input_str, char split_on,
                                                struct aws_array_list *output, size_t n);

/**
 * Copies from to to. If to is too small, AWS_ERROR_DEST_COPY_TOO_SMALL will be returned.
 * dest->len will contain the amount of data actually copied to dest.
 */
AWS_COMMON_API int aws_byte_buf_append(struct aws_byte_buf *to, struct aws_byte_cursor *from);

/**
 * Concatenates a variable number of struct aws_byte_buf * into destination. Number of args must be
 * greater than 1. If dest is too small, AWS_ERROR_DEST_COPY_TOO_SMALL will be returned. dest->len
 * will contain the amount of data actually copied to dest.
 */
AWS_COMMON_API int aws_byte_buf_cat(struct aws_byte_buf *dest, size_t number_of_args, ...);

#ifdef __cplusplus
}
#endif

static inline int aws_byte_buf_init(struct aws_allocator * allocator, struct aws_byte_buf * buf, size_t len) {
    buf->buffer = (uint8_t*)aws_mem_acquire(allocator, len);
    if (!buf->buffer) return aws_raise_error(AWS_ERROR_OOM);
    buf->len = 0;
    buf->capacity = len;
    buf->allocator = allocator;
    return AWS_OP_SUCCESS;
}

static inline void aws_byte_buf_clean_up(struct aws_byte_buf * buf) {
    if (buf->allocator && buf->buffer) aws_mem_release(buf->allocator, (void *)buf->buffer);
    buf->allocator = NULL;
    buf->buffer = NULL;
    buf->len = 0;
    buf->capacity = 0;
}

/**
 * For creating a byte buffer from a constant string. (With no nulls, else strlen will not work.)
 */
static inline struct aws_byte_buf aws_byte_buf_from_literal(const char *literal) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)literal;
    buf.len = strlen(literal);
    buf.capacity = buf.len;
    buf.allocator = NULL;
    return buf;
}

static inline struct aws_byte_buf aws_byte_buf_from_c_str(const char *c_str, size_t len) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)c_str;
    buf.len = len;
    buf.capacity = len;
    buf.allocator = NULL;
    return buf;
}

static inline struct aws_byte_buf aws_byte_buf_from_array(const uint8_t *c_str, size_t len) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)c_str;
    buf.len = len;
    buf.capacity = len;
    buf.allocator = NULL;
    return buf;
}

static inline struct aws_byte_cursor aws_byte_cursor_from_buf(const struct aws_byte_buf *buf) {
    struct aws_byte_cursor cur;
    cur.ptr = buf->buffer;
    cur.len = buf->len;
    return cur;
}

static inline struct aws_byte_cursor aws_byte_cursor_from_array(const uint8_t *c_str, size_t len) {
    struct aws_byte_cursor cur;
    cur.ptr = (uint8_t *)c_str;
    cur.len = len;
    return cur;
}

/**
 * If index >= bound, bound > (SIZE_MAX / 2), or index > (SIZE_MAX / 2), returns 0.
 * Otherwise, returns index.  This function is designed to return a value
 * within [0, bound) even under CPU speculation conditions, and is intended to
 * be used for SPECTRE mitigation purposes.
 */
static inline size_t aws_nospec_index(size_t index, size_t bound) {
    /*
     * SPECTRE mitigation - we compute a mask that will be zero if len < 0
     * or len >= buf->len, and all-ones otherwise, and AND it into the index.
     * It is critical that we avoid any branches in this logic.
     */

    /*
     * Hide the index value from the optimizer. This helps ensure that all this
     * logic doesn't get eliminated.
     */
#if defined(__GNUC__) || defined(__clang__)
     __asm__ __volatile__("" : "+r" (index));
#endif
#if defined(_MSVC_LANG)
     /*
      * MSVC doesn't have a good way for us to blind the optimizer, and doesn't
      * even have inline asm on x64. Some experimentation indicates that this
      * hack seems to confuse it sufficiently for our needs.
      */
     *((volatile uint8_t *)&index) += 0;
#endif

    /*
     * If len > (SIZE_MAX / 2), then we can end up with len - buf->len being
     * positive simply because the sign bit got inverted away. So we also check
     * that the sign bit isn't set from the start.
     *
     * We also check that bound <= (SIZE_MAX / 2) to catch cases where the buffer
     * is _already_ out of bounds.
     */
    size_t negative_mask = index | bound;
    size_t toobig_mask = bound - index - (uintptr_t)1;
    size_t combined_mask = negative_mask | toobig_mask;

    /*
     * combined_mask needs to have its sign bit OFF for us to be in range.
     * We'd like to expand this to a mask we can AND into our index, so flip
     * that bit (and everything else), shift it over so it's the only bit in the
     * ones position, and multiply across the entire register.
     *
     * First, extract the (inverse) top bit and move it to the lowest bit.
     * Because there's no standard SIZE_BIT in C99, we'll divide by a mask with
     * just the top bit set instead.
     */

    combined_mask = (~combined_mask) / (SIZE_MAX - (SIZE_MAX >> 1));

    /*
     * Now multiply it to replicate it across all bits.
     *
     * Note that GCC is smart enough to optimize the divide-and-multiply into
     * an arithmetic right shift operation on x86.
     */
    combined_mask = combined_mask * SIZE_MAX;

    return index & combined_mask;
}

/**
 * Tests if the given aws_byte_cursor has at least len bytes remaining. If so,
 * *buf is advanced by len bytes (incrementing ->ptr and decrementing ->len),
 * and an aws_byte_cursor referring to the first len bytes of the original *buf is
 * returned. Otherwise, an aws_byte_cursor with ->ptr = NULL, ->len = 0 is returned.
 *
 * Note that if len is above (SIZE_MAX / 2), this function will also treat it as a buffer
 * overflow, and return NULL without changing *buf.
 */
static inline struct aws_byte_cursor aws_byte_cursor_advance(struct aws_byte_cursor *cursor, size_t len) {
    struct aws_byte_cursor rv;
    if (cursor->len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || len > cursor->len) {
        rv.ptr = NULL;
        rv.len = 0;
    } else {
        rv.ptr = cursor->ptr;
        rv.len = len;

        cursor->ptr += len;
        cursor->len -= len;
    }

    return rv;
}

/**
 * Behaves identically to aws_byte_cursor_advance, but avoids speculative
 * execution potentially reading out-of-bounds pointers (by returning an
 * empty ptr in such speculated paths).
 *
 * This should generally be done when using an untrusted or
 * data-dependent value for 'len', to avoid speculating into a path where
 * cursor->ptr points outside the true ptr length.
 */

static inline struct aws_byte_cursor aws_byte_cursor_advance_nospec(struct aws_byte_cursor *cursor, size_t len) {
    struct aws_byte_cursor rv;

    if (len <= cursor->len && len <= (SIZE_MAX >> 1) && cursor->len <= (SIZE_MAX >> 1)) {
        /*
         * Pass the length through aws_nospec_index. We do this after the branch, as otherwise
         * we'd treat an out-of-bounds read as a zero-length read.
         */
        len = aws_nospec_index(len, cursor->len + 1);

        rv.ptr = cursor->ptr;
        rv.len = len;

        cursor->ptr += len;
        cursor->len -= len;
    } else {
        rv.ptr = NULL;
        rv.len = 0;
    }

    return rv;
}

/**
 * Reads specified length of data from byte cursor and copies it to the destination array.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read(struct aws_byte_cursor * AWS_RESTRICT cur, void * AWS_RESTRICT dest, size_t len) {
    struct aws_byte_cursor slice = aws_byte_cursor_advance_nospec(cur, len);

    if (slice.ptr) {
        memcpy(dest, slice.ptr, len);
        return true;
    } else {
        return false;
    }
}

/**
 * Reads as many bytes from cursor as size of buffer, and copies them to buffer.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read_and_fill_buffer(struct aws_byte_cursor * AWS_RESTRICT cur, struct aws_byte_buf * AWS_RESTRICT dest) {
    if (aws_byte_cursor_read(cur, dest->buffer, dest->capacity)) {
        dest->len = dest->capacity;
        return true;
    }
    return false;
}

/**
 * Reads a single byte from cursor, placing it in *var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read_u8(struct aws_byte_cursor * AWS_RESTRICT cur, uint8_t * AWS_RESTRICT var) {
    return aws_byte_cursor_read(cur, var, 1);
}

/**
 * Reads a 16-bit value in network byte order from cur, and places it in host byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read_be16(struct aws_byte_cursor *cur, uint16_t *var) {
    bool rv = aws_byte_cursor_read(cur, var, 2);

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh16(*var);
    }

    return rv;
}

/**
 * Reads a 32-bit value in network byte order from cur, and places it in host byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read_be32(struct aws_byte_cursor *cur, uint32_t *var) {
    bool rv = aws_byte_cursor_read(cur, var, 4);

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh32(*var);
    }

    return rv;
}

/**
 * Reads a 64-bit value in network byte order from cur, and places it in host byte order into var.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_read_be64(struct aws_byte_cursor *cur, uint64_t *var) {
    bool rv = aws_byte_cursor_read(cur, var, sizeof(*var));

    if (AWS_LIKELY(rv)) {
        *var = aws_ntoh64(*var);
    }

    return rv;
}

/**
 * Write specified number of bytes from array to byte cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write(struct aws_byte_cursor * AWS_RESTRICT cur, const uint8_t * AWS_RESTRICT src, size_t len) {
    struct aws_byte_cursor slice = aws_byte_cursor_advance_nospec(cur, len);

    if (slice.ptr) {
        memcpy(slice.ptr, src, len);
        return true;
    } else {
        return false;
    }
}

/**
 * Copies all bytes from buffer to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_from_whole_buffer(struct aws_byte_cursor * AWS_RESTRICT cur, const struct aws_byte_buf * AWS_RESTRICT src) {
    return aws_byte_cursor_write(cur, src->buffer, src->len);
}

/**
 * Copies all bytes from dynamic buffer to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_from_whole_string(struct aws_byte_cursor * AWS_RESTRICT cur, const struct aws_string * AWS_RESTRICT src) {
    return aws_byte_cursor_write(cur, aws_string_bytes(src), src->len);
}

/**
 * Copies one byte to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.<<<<<< str-split

 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_u8(struct aws_byte_cursor * AWS_RESTRICT cur, uint8_t c) {
    return aws_byte_cursor_write(cur, &c, 1);
}

/**
 * Writes a 16-bit integer in network byte order (big endian) to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_be16(struct aws_byte_cursor *cur, uint16_t x) {
    x = aws_hton16(x);
    return aws_byte_cursor_write(cur, (uint8_t *) &x, 2);
}

/**
 * Writes a 32-bit integer in network byte order (big endian) to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_be32(struct aws_byte_cursor *cur, uint32_t x) {
    x = aws_hton32(x);
    return aws_byte_cursor_write(cur, (uint8_t *) &x, 4);
}

/**
 * Writes a 64-bit integer in network byte order (big endian) to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
 * If there is insufficient space in the cursor, returns false, leaving the cursor unchanged.
 */
static inline bool aws_byte_cursor_write_be64(struct aws_byte_cursor *cur, uint64_t x) {
    x = aws_hton64(x);
    return aws_byte_cursor_write(cur, (uint8_t *) &x, 8);
}

#endif /* AWS_COMMON_BYTE_BUF_H */
