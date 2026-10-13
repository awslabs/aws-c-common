/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/big.h>

#include <aws/common/math.h>
#include <aws/common/private/big.h>
#include <aws/common/private/byte_buf.h>

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

struct aws_big_integer {
    struct aws_allocator *allocator;

    uint64_t *abs; // zero => abs == NULL && abslen == 0
    size_t abslen; // in u64 words

    bool is_negative;
};

struct aws_big_decimal {
    struct aws_big_integer mantissa;
    int64_t exponent;
};

// -9223372036854775808 is 20 chars + snprintf NULL
enum { I64_MAX_BUFLEN = 21 };

// bigint atoi happens in chunks of 10^19 (biggest E that fits in u64)
enum { CHUNK_DIGITS = 19 };

// 10^19 and its inverse
static const uint64_t CHUNK_BASE = 10000000000000000000ULL;
static const uint64_t CHUNK_BASE_RECIPROCAL = 0xd83c94fb6d2ac34aULL;

/*
 * Digit<->word conversion Horner-based i.e. O(n^2) so we impose length limits, see
 * https://nvd.nist.gov/vuln/detail/cve-2020-10735.
 *
 * The limit is primarily defined by MAX_BYTES, at 4096 that is 512 64-bit words, or ~9865 digits, compared to Python's
 * default limit of 4300. 512 words benchmarks comparably to Python at its default limit on my M3 Pro, so basically we
 * will only ever be about as slow as Python's default but we support >2x the length.
 *
 * If we adopt faster algorithms these limits can probably either increase or go away.
 */
enum {
    MAX_BYTES = AWS_BIG_INTEGER_MAX_BYTES,
    MAX_DIGITS = 9865,
    MAX_WORDS = MAX_BYTES / sizeof(uint64_t),
};

// "how many u64 words do i need for this digit string"
// int approximation of exact: ceil(digits * log2(10) / 64)
static size_t s_max_abslen(size_t digits) {
    uint64_t scaled = (uint64_t)digits * 217706;
    return (size_t)((scaled + ((UINT64_C(1) << 22) - 1)) >> 22);
}

// "how many chars do i need to stringify these u64 words" (minus sign, which is checked by caller)
// int approximation of exact: floor(bits * log10(2)) + 1
static size_t s_max_strlen(size_t numwords, uint64_t top_word) {
    if (numwords == 0) {
        return 1;
    }

    uint64_t bits = ((uint64_t)(numwords - 1) * 64) + (64 - aws_clz_u64(top_word));
    return (size_t)((bits * 78914) >> 18) + 1;
}

struct s_uint128 {
    uint64_t hi;
    uint64_t lo;
};

static struct s_uint128 s_mul_u128(uint64_t a, uint64_t b) {
    const uint64_t mask = 0xffffffffULL;
    uint64_t a_lo = a & mask;
    uint64_t a_hi = a >> 32;
    uint64_t b_lo = b & mask;
    uint64_t b_hi = b >> 32;

    uint64_t lo_lo = a_lo * b_lo;
    uint64_t lo_hi = a_lo * b_hi;
    uint64_t hi_lo = a_hi * b_lo;
    uint64_t hi_hi = a_hi * b_hi;

    uint64_t middle = (lo_lo >> 32) + (lo_hi & mask) + (hi_lo & mask);
    struct s_uint128 result;
    result.hi = hi_hi + (lo_hi >> 32) + (hi_lo >> 32) + (middle >> 32);
    result.lo = (middle << 32) | (lo_lo & mask);
    return result;
}

static struct s_uint128 s_add_u128(struct s_uint128 a, struct s_uint128 b) {
    struct s_uint128 result;
    result.lo = a.lo + b.lo;
    result.hi = a.hi + b.hi + (result.lo < a.lo);
    return result;
}

static uint64_t s_div_u128(struct s_uint128 u, uint64_t d, uint64_t v, uint64_t *remainder) {
    struct s_uint128 q = s_add_u128(s_mul_u128(v, u.hi), u);
    q.hi += 1;

    uint64_t r = u.lo - (q.hi * d);
    if (r > q.lo) {
        q.hi -= 1;
        r += d;
    }
    if (r >= d) {
        q.hi += 1;
        r -= d;
    }

    *remainder = r;
    return q.hi;
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

static uint64_t s_take_chunk(struct aws_byte_cursor *first, struct aws_byte_cursor *second, size_t len) {
    uint64_t chunk = 0;
    while (len > 0) {
        struct aws_byte_cursor *src = first->len > 0 ? first : second;
        size_t take = len < src->len ? len : src->len;
        for (size_t i = 0; i < take; ++i) {
            chunk = (chunk * 10) + (uint64_t)(src->ptr[i] - '0');
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
    uint64_t *words = aws_mem_calloc(allocator, s_max_abslen(digit_count), sizeof(uint64_t));
    if (words == NULL) {
        return AWS_OP_ERR;
    }

    size_t word_count = 0;
    size_t chunk_len = digit_count % CHUNK_DIGITS == 0 ? CHUNK_DIGITS : digit_count % CHUNK_DIGITS;
    for (size_t c = 0; c < nchunk; ++c) {
        uint64_t carry = s_take_chunk(&whole, &frac, chunk_len);
        for (size_t i = 0; i < word_count; ++i) {
            struct s_uint128 prod =
                s_add_u128(s_mul_u128(words[i], CHUNK_BASE), (struct s_uint128){.hi = 0, .lo = carry});
            words[i] = prod.lo;
            carry = prod.hi;
        }
        if (carry != 0) {
            if (word_count == MAX_WORDS) {
                aws_mem_release(allocator, words);
                return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
            }
            words[word_count++] = carry;
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

static int s_big_integer_itoa(
    const struct aws_big_integer *v,
    uint8_t *region,
    size_t region_len,
    size_t *digits_len) {

    if (v->abslen == 0) {
        if (region_len < 1) {
            return aws_raise_error(AWS_ERROR_DEST_COPY_TOO_SMALL);
        }
        region[region_len - 1] = '0';
        *digits_len = 1;
        return AWS_OP_SUCCESS;
    }

    size_t n = v->abslen;

    // conversion algorithm is destructive to the words, we have to alloc a working copy
    uint64_t *scratch = aws_mem_acquire(v->allocator, n * sizeof(uint64_t));
    if (scratch == NULL) {
        return AWS_OP_ERR;
    }

    memcpy(scratch, v->abs, n * sizeof(uint64_t));

    int result = AWS_OP_ERR;
    size_t pos = region_len;
    size_t count = n;
    while (count > 0) {
        uint64_t rem = 0;
        for (size_t i = count; i-- > 0;) {
            scratch[i] = s_div_u128((struct s_uint128){.hi = rem, .lo = scratch[i]}, CHUNK_BASE, CHUNK_BASE_RECIPROCAL, &rem);
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

    if (!aws_byte_cursor_is_valid(&bytes)) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    while (bytes.len > 0 && bytes.ptr[0] == 0) {
        aws_byte_cursor_advance(&bytes, 1);
    }

    if (bytes.len > MAX_BYTES) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_big_integer *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_integer));
    if (v == NULL) {
        return NULL;
    }
    v->allocator = allocator;

    if (bytes.len == 0) {
        return v;
    }

    size_t word_count = (bytes.len + 7) / 8;
    v->abs = aws_mem_calloc(allocator, word_count, sizeof(uint64_t));
    if (v->abs == NULL) {
        aws_mem_release(allocator, v);
        return NULL;
    }

    for (size_t i = 0; i < bytes.len; ++i) {
        uint64_t byte = bytes.ptr[bytes.len - 1 - i];
        v->abs[i / 8] |= byte << (8 * (i % 8));
    }

    v->abslen = word_count;
    v->is_negative = is_negative;
    return v;
}

struct aws_big_integer *aws_big_integer_new_from_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor cursor) {
    AWS_PRECONDITION(allocator);

    if (!aws_byte_cursor_is_valid(&cursor)) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    bool is_neg = s_take_sign(&cursor);
    struct aws_byte_cursor digits = s_take_digits(&cursor);
    if (digits.len == 0 || cursor.len != 0) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_big_integer *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_integer));
    if (v == NULL) {
        return NULL;
    }

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

    uint64_t top = v->abs[v->abslen - 1];
    size_t top_bytes = 8;
    while (top_bytes > 1 && (top >> (8 * (top_bytes - 1))) == 0) {
        --top_bytes;
    }
    size_t total_bytes = ((v->abslen - 1) * 8) + top_bytes;

    if (s_ensure_capacity(out, total_bytes)) {
        return AWS_OP_ERR;
    }

    for (size_t i = total_bytes; i-- > 0;) {
        aws_byte_buf_write_u8(out, (uint8_t)(v->abs[i / 8] >> (8 * (i % 8))));
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

int aws_big_integer_to_str(const struct aws_big_integer *v, struct aws_byte_buf *out) {
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
    if (v == NULL) {
        return NULL;
    }
    v->mantissa.allocator = allocator;
    v->exponent = exponent;

    if (mantissa->abslen > 0) {
        v->mantissa.abs = aws_mem_calloc(allocator, mantissa->abslen, sizeof(uint64_t));
        if (v->mantissa.abs == NULL) {
            aws_mem_release(allocator, v);
            return NULL;
        }
        memcpy(v->mantissa.abs, mantissa->abs, mantissa->abslen * sizeof(uint64_t));
        v->mantissa.abslen = mantissa->abslen;
        v->mantissa.is_negative = mantissa->is_negative;
    }

    return v;
}

struct aws_big_decimal *aws_big_decimal_new_from_cursor(
    struct aws_allocator *allocator,
    struct aws_byte_cursor cursor) {
    AWS_PRECONDITION(allocator);

    if (!aws_byte_cursor_is_valid(&cursor)) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

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

    if (exp < INT64_MIN + (int64_t)frac.len) { // biasing exp would underflow
        aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
        return NULL;
    }

    exp -= (int64_t)frac.len;

    struct aws_big_decimal *v = aws_mem_calloc(allocator, 1, sizeof(struct aws_big_decimal));
    if (v == NULL) {
        return NULL;
    }

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

    // <mant w/ sign> .. e .. <exp w/ sign>
    return aws_big_integer_max_strlen(&v->mantissa) + 1 + exponent_len;
}

int aws_big_decimal_to_str(const struct aws_big_decimal *v, struct aws_byte_buf *out) {
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
