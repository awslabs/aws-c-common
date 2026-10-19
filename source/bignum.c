/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/bignum.h>

#include <aws/common/math.h>
#include <aws/common/private/byte_buf.h>

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

struct aws_big_integer {
    struct aws_allocator *allocator;

    uint32_t *abs; /* zero => abs == NULL && abslen == 0 */
    size_t abslen; /* in u32 words */

    bool is_negative;
};

struct aws_big_decimal {
    struct aws_big_integer mantissa;
    int64_t exponent;
};

/* -9223372036854775808 is 20 chars + snprintf NULL */
enum { I64_MAX_BUFLEN = 21 };

/*
 * Words are 32 bits so that every intermediate product, sum and quotient fits in a native uint64_t.
 *
 * bigint atoi/itoa happens in chunks of 10^9 (biggest E that fits in u32).
 */
enum {
    CHUNK_DIGITS = 9,
    CHUNK_BASE = 1000000000,
};

/*
 * Digit<->word conversion Horner-based i.e. O(n^2) so we impose length limits, see
 * https://nvd.nist.gov/vuln/detail/cve-2020-10735.
 *
 * The limit is primarily defined by MAX_BYTES, at 2048 that is 256 64-bit words, or ~4933 digits, compared to Python's
 * default limit of 4300.
 *
 * If we adopt faster algorithms these limits can probably either increase or go away.
 */
enum {
    MAX_BYTES = 2048,
    MAX_DIGITS = 4933,
    MAX_WORDS = MAX_BYTES / sizeof(uint32_t),
};

/*
 * "how many u32 words do i need for this digit string"
 * int approximation of exact: ceil(digits * log2(10) / 32)
 */
static size_t s_max_abslen(size_t digits) {
    uint64_t scaled = (uint64_t)digits * 435412;
    return (size_t)((scaled + ((UINT64_C(1) << 22) - 1)) >> 22);
}

/*
 * "how many chars do i need to stringify these u32 words" (minus sign, which is checked by caller)
 * int approximation of exact: floor(bits * log10(2)) + 1
 */
static size_t s_max_strlen(size_t numwords, uint32_t top_word) {
    if (numwords == 0) {
        return 1;
    }

    uint64_t bits = ((uint64_t)(numwords - 1) * 32) + (32 - aws_clz_u32(top_word));
    return (size_t)((bits * 78914) >> 18) + 1;
}

static bool s_is_zero_byte(uint8_t c) {
    return c == 0;
}

static bool s_ischar(struct aws_byte_cursor *c, uint8_t v) {
    return c->len > 0 && c->ptr[0] == v;
}

static bool s_isexp(struct aws_byte_cursor *c) {
    return c->len > 0 && (c->ptr[0] == 'e' || c->ptr[0] == 'E');
}

static bool s_take_sign(struct aws_byte_cursor *c) {
    if (c->len == 0) {
        return false;
    }
    if (c->ptr[0] == '-') {
        aws_byte_cursor_advance(c, 1);
        return true;
    }
    if (c->ptr[0] == '+') {
        aws_byte_cursor_advance(c, 1);
    }
    return false;
}

static struct aws_byte_cursor s_take_digits(struct aws_byte_cursor *c) {
    size_t len = 0;
    while (len < c->len && aws_isdigit(c->ptr[len])) {
        ++len;
    }
    return aws_byte_cursor_advance(c, len);
}

static uint32_t s_take_chunk(struct aws_byte_cursor *first, struct aws_byte_cursor *second, size_t len) {
    uint32_t chunk = 0;
    while (len > 0) {
        struct aws_byte_cursor *src = first->len > 0 ? first : second;
        size_t take = len < src->len ? len : src->len;
        for (size_t i = 0; i < take; ++i) {
            chunk = (chunk * 10) + (uint32_t)(src->ptr[i] - '0');
        }
        src->ptr += take;
        src->len -= take;
        len -= take;
    }
    return chunk;
}

static void s_big_integer_clean_up(struct aws_big_integer *v) {
    if (v->abs != NULL) {
        aws_mem_release(v->allocator, v->abs);
    }
    AWS_ZERO_STRUCT(*v);
}

static int s_big_integer_atoi(
    struct aws_big_integer *v,
    struct aws_allocator *allocator,
    bool is_negative,
    struct aws_byte_cursor whole,
    struct aws_byte_cursor frac) {

    AWS_ZERO_STRUCT(*v);
    v->allocator = allocator;

    while (whole.len > 0 && whole.ptr[0] == '0') {
        aws_byte_cursor_advance(&whole, 1);
    }
    if (whole.len == 0) {
        while (frac.len > 0 && frac.ptr[0] == '0') {
            aws_byte_cursor_advance(&frac, 1);
        }
    }

    size_t digit_count = whole.len + frac.len;
    if (digit_count > MAX_DIGITS) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }
    if (digit_count == 0) {
        return AWS_OP_SUCCESS;
    }

    size_t nchunk = (digit_count + CHUNK_DIGITS - 1) / CHUNK_DIGITS;
    uint32_t *words = aws_mem_calloc(allocator, s_max_abslen(digit_count), sizeof(uint32_t));

    size_t word_count = 0;
    size_t chunk_len = digit_count % CHUNK_DIGITS == 0 ? CHUNK_DIGITS : digit_count % CHUNK_DIGITS;
    for (size_t c = 0; c < nchunk; ++c) {
        uint64_t carry = s_take_chunk(&whole, &frac, chunk_len);
        for (size_t i = 0; i < word_count; ++i) {
            uint64_t prod = ((uint64_t)words[i] * CHUNK_BASE) + carry;
            words[i] = (uint32_t)prod;
            carry = prod >> 32;
        }
        if (carry != 0) {
            if (word_count == MAX_WORDS) {
                aws_mem_release(allocator, words);
                return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
            }
            words[word_count++] = (uint32_t)carry;
        }
        chunk_len = CHUNK_DIGITS;
    }

    v->abs = words;
    v->abslen = word_count;
    v->is_negative = is_negative;
    return AWS_OP_SUCCESS;
}

static int s_ensure_capacity(struct aws_byte_buf *out, size_t additional) {
    if (out->allocator != NULL) {
        return aws_byte_buf_reserve_smart_relative(out, additional);
    }

    if (out->capacity - out->len < additional) {
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }
    return AWS_OP_SUCCESS;
}

static int s_big_integer_itoa(const struct aws_big_integer *v, uint8_t *region, size_t region_len, size_t *digits_len) {

    if (v->abslen == 0) {
        if (region_len < 1) {
            return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
        }
        region[region_len - 1] = '0';
        *digits_len = 1;
        return AWS_OP_SUCCESS;
    }

    size_t n = v->abslen;

    /* conversion algorithm is destructive to the words, we have to alloc a working copy */
    uint32_t *scratch = aws_mem_acquire(v->allocator, n * sizeof(uint32_t));

    memcpy(scratch, v->abs, n * sizeof(uint32_t));

    int result = AWS_OP_ERR;
    size_t pos = region_len;
    size_t count = n;
    while (count > 0) {
        uint64_t rem = 0;
        for (size_t i = count; i-- > 0;) {
            uint64_t cur = (rem << 32) | scratch[i];
            scratch[i] = (uint32_t)(cur / CHUNK_BASE);
            rem = cur % CHUNK_BASE;
        }
        while (count > 0 && scratch[count - 1] == 0) {
            --count;
        }

        size_t chunk_digits = count > 0 ? CHUNK_DIGITS : 0;
        for (size_t d = 0; d < CHUNK_DIGITS && (d < chunk_digits || rem != 0); ++d) {
            if (pos == 0) {
                aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
                goto done;
            }
            region[--pos] = (uint8_t)('0' + (rem % 10));
            rem /= 10;
        }
    }

    *digits_len = region_len - pos;
    result = AWS_OP_SUCCESS;

done:
    aws_mem_release(v->allocator, scratch);
    return result;
}

static int s_big_integer_to_base10(const struct aws_big_integer *v, struct aws_byte_buf *out, size_t suffix_len) {
    size_t sign_len = v->is_negative ? 1 : 0;
    size_t max_digits = s_max_strlen(v->abslen, v->abslen > 0 ? v->abs[v->abslen - 1] : 0);

    if (out->allocator != NULL && aws_byte_buf_reserve_smart_relative(out, sign_len + max_digits + suffix_len)) {
        return AWS_OP_ERR;
    }

    size_t spare = out->capacity - out->len;
    if (spare < sign_len + suffix_len + 1) {
        return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
    }

    size_t region_len = spare - sign_len - suffix_len;
    if (region_len > max_digits) {
        region_len = max_digits;
    }

    uint8_t *region = out->buffer + out->len + sign_len;
    size_t digits_len = 0;
    if (s_big_integer_itoa(v, region, region_len, &digits_len)) {
        return AWS_OP_ERR;
    }

    if (sign_len) {
        out->buffer[out->len] = '-';
    }
    memmove(region, region + region_len - digits_len, digits_len);
    out->len += sign_len + digits_len;
    return AWS_OP_SUCCESS;
}

static int s_compare_magnitude(const struct aws_big_integer *a, const struct aws_big_integer *b) {
    if (a->abslen != b->abslen) {
        return a->abslen < b->abslen ? -1 : 1;
    }

    for (size_t i = a->abslen; i-- > 0;) {
        if (a->abs[i] != b->abs[i]) {
            return a->abs[i] < b->abs[i] ? -1 : 1;
        }
    }
    return 0;
}

struct aws_big_integer *aws_big_integer_new(
    struct aws_allocator *allocator,
    struct aws_byte_cursor bytes,
    bool is_negative) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&bytes));

    bytes = aws_byte_cursor_left_trim_pred(&bytes, s_is_zero_byte);

    if (bytes.len > MAX_BYTES) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_big_integer *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_integer));
    v->allocator = allocator;

    if (bytes.len == 0) {
        return v;
    }

    size_t word_count = (bytes.len + 3) / 4;
    v->abs = aws_mem_calloc(allocator, word_count, sizeof(uint32_t));

    for (size_t i = 0; i < bytes.len; ++i) {
        uint32_t byte = bytes.ptr[bytes.len - 1 - i];
        v->abs[i / 4] |= byte << (8 * (i % 4));
    }

    v->abslen = word_count;
    v->is_negative = is_negative;
    return v;
}

struct aws_big_integer *aws_big_integer_new_from_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor cursor) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&cursor));

    bool is_neg = s_take_sign(&cursor);
    struct aws_byte_cursor digits = s_take_digits(&cursor);
    if (digits.len == 0 || cursor.len != 0) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_big_integer *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_integer));

    struct aws_byte_cursor nil;
    AWS_ZERO_STRUCT(nil);
    if (s_big_integer_atoi(v, allocator, is_neg, digits, nil)) {
        aws_mem_release(allocator, v);
        return NULL;
    }

    return v;
}

void aws_big_integer_destroy(struct aws_big_integer *v) {
    if (v == NULL) {
        return;
    }

    struct aws_allocator *allocator = v->allocator;
    s_big_integer_clean_up(v);
    aws_mem_release(allocator, v);
}

int aws_big_integer_get_magnitude_be(const struct aws_big_integer *v, struct aws_byte_buf *out) {
    AWS_PRECONDITION(v);
    AWS_PRECONDITION(aws_byte_buf_is_valid(out));

    if (v->abslen == 0) {
        return AWS_OP_SUCCESS;
    }

    uint32_t top = v->abs[v->abslen - 1];
    size_t top_bytes = 4;
    while (top_bytes > 1 && (top >> (8 * (top_bytes - 1))) == 0) {
        --top_bytes;
    }
    size_t total_bytes = ((v->abslen - 1) * 4) + top_bytes;

    if (s_ensure_capacity(out, total_bytes)) {
        return AWS_OP_ERR;
    }

    for (size_t i = total_bytes; i-- > 0;) {
        aws_byte_buf_write_u8(out, (uint8_t)(v->abs[i / 4] >> (8 * (i % 4))));
    }
    return AWS_OP_SUCCESS;
}

int aws_big_integer_get_sign(const struct aws_big_integer *v) {
    AWS_PRECONDITION(v);

    if (v->abslen == 0) {
        return 0;
    }
    return v->is_negative ? -1 : 1;
}

bool aws_big_integer_eq(const struct aws_big_integer *a, const struct aws_big_integer *b) {
    AWS_PRECONDITION(a);
    AWS_PRECONDITION(b);

    return a->is_negative == b->is_negative && s_compare_magnitude(a, b) == 0;
}

size_t aws_big_integer_max_strlen(const struct aws_big_integer *v) {
    AWS_PRECONDITION(v);

    size_t max_digits = s_max_strlen(v->abslen, v->abslen > 0 ? v->abs[v->abslen - 1] : 0);
    return max_digits + (v->is_negative ? 1 : 0);
}

int aws_byte_buf_append_big_integer(struct aws_byte_buf *out, const struct aws_big_integer *v) {
    AWS_PRECONDITION(v);
    AWS_PRECONDITION(aws_byte_buf_is_valid(out));

    return s_big_integer_to_base10(v, out, 0);
}

struct aws_big_decimal *aws_big_decimal_new(
    struct aws_allocator *allocator,
    const struct aws_big_integer *mantissa,
    int64_t exponent) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(mantissa);

    struct aws_big_decimal *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_decimal));
    v->mantissa.allocator = allocator;
    v->exponent = exponent;

    if (mantissa->abslen > 0) {
        v->mantissa.abs = aws_mem_calloc(allocator, mantissa->abslen, sizeof(uint32_t));
        memcpy(v->mantissa.abs, mantissa->abs, mantissa->abslen * sizeof(uint32_t));
        v->mantissa.abslen = mantissa->abslen;
        v->mantissa.is_negative = mantissa->is_negative;
    }

    return v;
}

struct aws_big_decimal *aws_big_decimal_new_from_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor cursor) {
    AWS_PRECONDITION(allocator);
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&cursor));

    bool is_negative = s_take_sign(&cursor);
    struct aws_byte_cursor whole = s_take_digits(&cursor);
    if (whole.len == 0) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_byte_cursor frac;
    AWS_ZERO_STRUCT(frac);
    if (s_ischar(&cursor, '.')) {
        aws_byte_cursor_advance(&cursor, 1);

        frac = s_take_digits(&cursor);
        if (frac.len == 0) {
            aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
            return NULL;
        }
    }

    int64_t exp = 0;
    if (s_isexp(&cursor)) {
        aws_byte_cursor_advance(&cursor, 1);

        bool exp_is_negative = s_take_sign(&cursor);
        struct aws_byte_cursor exp_digits = s_take_digits(&cursor);
        if (exp_digits.len == 0 || cursor.len != 0) {
            aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
            return NULL;
        }

        uint64_t exp_magnitude = 0;
        if (aws_byte_cursor_utf8_parse_u64(exp_digits, &exp_magnitude)) {
            return NULL;
        }

        if (exp_is_negative && exp_magnitude == (uint64_t)INT64_MAX + 1) {
            exp = INT64_MIN;
        } else if (exp_magnitude > (uint64_t)INT64_MAX) {
            aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
            return NULL;
        } else {
            exp = exp_is_negative ? -(int64_t)exp_magnitude : (int64_t)exp_magnitude;
        }
    } else if (cursor.len != 0) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    if (exp < INT64_MIN + (int64_t)frac.len) { /* biasing exp would underflow */
        aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
        return NULL;
    }

    exp -= (int64_t)frac.len;

    struct aws_big_decimal *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_decimal));

    if (s_big_integer_atoi(&v->mantissa, allocator, is_negative, whole, frac)) {
        aws_mem_release(allocator, v);
        return NULL;
    }

    v->exponent = exp;
    return v;
}

void aws_big_decimal_destroy(struct aws_big_decimal *v) {
    if (v == NULL) {
        return;
    }

    struct aws_allocator *allocator = v->mantissa.allocator;
    s_big_integer_clean_up(&v->mantissa);
    aws_mem_release(allocator, v);
}

const struct aws_big_integer *aws_big_decimal_get_mantissa(const struct aws_big_decimal *v) {
    AWS_PRECONDITION(v);
    return &v->mantissa;
}

int64_t aws_big_decimal_get_exponent(const struct aws_big_decimal *v) {
    AWS_PRECONDITION(v);
    return v->exponent;
}

bool aws_big_decimal_eq(const struct aws_big_decimal *a, const struct aws_big_decimal *b) {
    AWS_PRECONDITION(a);
    AWS_PRECONDITION(b);

    return a->exponent == b->exponent && aws_big_integer_eq(&a->mantissa, &b->mantissa);
}

size_t aws_big_decimal_max_strlen(const struct aws_big_decimal *v) {
    AWS_PRECONDITION(v);

    uint64_t exponent_magnitude = v->exponent < 0 ? (uint64_t)0 - (uint64_t)v->exponent : (uint64_t)v->exponent;
    size_t exponent_len = v->exponent < 0 ? 1 : 0;
    do {
        ++exponent_len;
        exponent_magnitude /= 10;
    } while (exponent_magnitude != 0);

    /* <mant w/ sign> .. e .. <exp w/ sign> */
    return aws_big_integer_max_strlen(&v->mantissa) + 1 + exponent_len;
}

int aws_byte_buf_append_big_decimal(struct aws_byte_buf *out, const struct aws_big_decimal *v) {
    AWS_PRECONDITION(v);
    AWS_PRECONDITION(aws_byte_buf_is_valid(out));

    char exponent_str[I64_MAX_BUFLEN];
    int exponent_len = snprintf(exponent_str, sizeof(exponent_str), "%" PRId64, v->exponent);
    if (exponent_len < 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    if (s_big_integer_to_base10(&v->mantissa, out, 1 + (size_t)exponent_len)) {
        return AWS_OP_ERR;
    }

    aws_byte_buf_write_u8(out, 'e');
    aws_byte_buf_write(out, (const uint8_t *)exponent_str, (size_t)exponent_len);
    return AWS_OP_SUCCESS;
}
