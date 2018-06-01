#ifndef AWS_STRING_H
#define AWS_STRING_H
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
#include <aws/common/byte_order.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>

/**
 * Represents a length-delimited binary string or buffer. If byte buffer points to constant
 * memory or memory that should otherwise not be freed by this struct, set allocator to NULL
 * and free function will be a no-op.
 */
struct aws_byte_buf {
    struct aws_allocator * allocator;
    uint8_t *buffer;
    size_t len;
};

static inline int aws_byte_buf_init(struct aws_allocator * allocator, struct aws_byte_buf * buf, size_t len) {
    buf->buffer = (uint8_t*)allocator->mem_acquire(allocator, len);
    if (!buf->buffer) return aws_raise_error(AWS_ERROR_OOM);
    buf->len = len;
    buf->allocator = allocator;
    return AWS_OP_SUCCESS;
}

static inline void aws_byte_buf_clean_up(struct aws_byte_buf * buf) {
    if (buf->allocator && buf->buffer) buf->allocator->mem_release(buf->allocator, buf->buffer);
    buf->allocator = NULL;
    buf->buffer = NULL;
    buf->len = 0;
}

/**
 * For creating a byte buffer from a constant string. (With no nulls, else strlen will not work.)
 */
static inline struct aws_byte_buf aws_byte_buf_from_literal(const char *literal) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)literal;
    buf.len = strlen(literal);
    buf.allocator = NULL;
    return buf;
}

static inline struct aws_byte_buf aws_byte_buf_from_c_str(const char *c_str, size_t len) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)c_str;
    buf.len = len;
    buf.allocator = NULL;
    return buf;
}

static inline struct aws_byte_buf aws_byte_buf_from_array(const uint8_t *c_str, size_t len) {
    struct aws_byte_buf buf;
    buf.buffer = (uint8_t *)c_str;
    buf.len = len;
    buf.allocator = NULL;
    return buf;
}

/**
 * Represents a movable pointer within a larger binary string or buffer.
 */
struct aws_byte_cursor {
    uint8_t *ptr;
    size_t len;
};

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
    return aws_byte_cursor_read(cur, dest->buffer, dest->len);
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
 * Copies one byte to cursor.
 *
 * On success, returns true and updates the cursor pointer/length accordingly.
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


#endif /* AWS_STRING_H */
