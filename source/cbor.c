#include "external/libcbor/cbor.h"
#include <aws/common/cbor.h>

#include <aws/common/array_list.h>
#include <aws/common/private/json_impl.h>
#include <aws/common/ref_count.h>
#include <fenv.h>
#include <math.h>

static struct aws_allocator *s_aws_cbor_module_allocator = NULL;
static bool s_aws_cbor_module_initialized = false;

void aws_cbor_module_init(struct aws_allocator *allocator) {
    if (!s_aws_cbor_module_initialized) {
        s_aws_cbor_module_allocator = allocator;
        /* Not allow any allocation from libcbor */
        cbor_set_allocs(NULL, NULL, NULL);
        s_aws_cbor_module_initialized = true;
    }
}

void aws_cbor_module_cleanup(void) {
    if (s_aws_cbor_module_initialized) {
        s_aws_cbor_module_allocator = NULL;
        s_aws_cbor_module_initialized = false;
    }
}

/*******************************************************************************
 * ENCODE
 ******************************************************************************/

struct aws_cbor_encoder {
    struct aws_allocator *allocator;

    /* Refcount maybe */
    struct aws_ref_count refcount;
    struct aws_byte_buf encoded_buf;
};

struct aws_cbor_encoder *aws_cbor_encoder_new(struct aws_allocator *allocator, size_t init_buffer_size) {
    struct aws_cbor_encoder *encoder = aws_mem_acquire(allocator, sizeof(struct aws_cbor_encoder));
    encoder->allocator = allocator;
    aws_byte_buf_init(&encoder->encoded_buf, allocator, init_buffer_size);

    /* TODO: refcount */
    return encoder;
}

struct aws_cbor_encoder *aws_cbor_encoder_release(struct aws_cbor_encoder *encoder) {
    aws_byte_buf_clean_up(&encoder->encoded_buf);
    aws_mem_release(encoder->allocator, encoder);
    return NULL;
}

struct aws_byte_cursor aws_cbor_encoder_get_encoded_data(struct aws_cbor_encoder *encoder) {
    return aws_byte_cursor_from_buf(&encoder->encoded_buf);
}

void aws_cbor_encoder_clear_encoded_data(struct aws_cbor_encoder *encoder) {
    aws_byte_buf_reset(&encoder->encoded_buf, false);
}

#define ENCODE_THROUGH_LIBCBOR(length_to_reserve, encoder, value, fn)                                                  \
    do {                                                                                                               \
        aws_byte_buf_reserve_dynamic(&(encoder)->encoded_buf, (encoder)->encoded_buf.len + (length_to_reserve));       \
        size_t encoded_len =                                                                                           \
            fn(value,                                                                                                  \
               (encoder)->encoded_buf.buffer + (encoder)->encoded_buf.len,                                             \
               (encoder)->encoded_buf.capacity - (encoder)->encoded_buf.len);                                          \
        AWS_ASSERT((encoded_len) != 0);                                                                                \
        (encoder)->encoded_buf.len += (encoded_len);                                                                   \
    } while (false)

void aws_cbor_encode_uint(struct aws_cbor_encoder *encoder, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_uint);
}

void aws_cbor_encode_negint(struct aws_cbor_encoder *encoder, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_negint);
}

void aws_cbor_encode_single_float(struct aws_cbor_encoder *encoder, float value) {
    ENCODE_THROUGH_LIBCBOR(5, encoder, value, cbor_encode_single);
}

void aws_cbor_encode_double(struct aws_cbor_encoder *encoder, double value) {
    if (isnan(value) || isinf(value)) {
        /* For special value: NAN/INFINITY, type cast to float and encode into single float. */
        aws_cbor_encode_single_float(encoder, (float)value);
        return;
    }

    int64_t int_value = llround(value);
    /* Ignore the possible exception raised from llround. */
    feclearexcept(FE_ALL_EXCEPT);

    if (value == (double)int_value) {
        if (int_value < 0) {
            aws_cbor_encode_negint(encoder, (uint64_t)(-1 * int_value));
        } else {
            aws_cbor_encode_uint(encoder, (uint64_t)(int_value));
        }
        return;
    }
    /* TODO: If the value being converted is outside the range of values that can be represented, the behavior is
     * undefined? */
    float float_value = (float)value;
    double converted_value = (double)float_value;
    if (value == converted_value) {
        aws_cbor_encode_single_float(encoder, float_value);
        return;
    }

    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_double);
}

void aws_cbor_encode_map_start(struct aws_cbor_encoder *encoder, size_t number_entries) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, number_entries, cbor_encode_map_start);
}

void aws_cbor_encode_tag(struct aws_cbor_encoder *encoder, uint64_t tag_number) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, tag_number, cbor_encode_tag);
}

void aws_cbor_encode_array_start(struct aws_cbor_encoder *encoder, size_t number_entries) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, number_entries, cbor_encode_array_start);
}

void aws_cbor_encode_bytes(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from) {
    /* Reserve the bytes for the byte string start cbor item and the actual bytes */
    /* Encode the first cbor item for byte string */
    ENCODE_THROUGH_LIBCBOR(9 + from->len, encoder, from->len, cbor_encode_bytestring_start);
    /* Append the actual bytes to follow the cbor item */
    aws_byte_buf_append(&encoder->encoded_buf, from);
}

void aws_cbor_encode_string(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from) {
    /* Reserve the bytes for the byte string start cbor item and the actual string */
    /* Encode the first cbor item for byte string */
    ENCODE_THROUGH_LIBCBOR(9 + from->len, encoder, from->len, cbor_encode_string_start);
    /* Append the actual string to follow the cbor item */
    aws_byte_buf_append(&encoder->encoded_buf, from);
}

void aws_cbor_encode_epoch_timestamp_secs(struct aws_cbor_encoder *encoder, double epoch_time_secs) {
    /* Encode the tag cbor item with tag value 1, as Epoch-based date/time */
    ENCODE_THROUGH_LIBCBOR(1, encoder, 1, cbor_encode_tag);
    /* Encode the tag content item as unsigned or negative integer (major types 0 and 1) or a floating-point number
     * (major type 7 with additional information 25, 26, or 27) */
    aws_cbor_encode_double(encoder, epoch_time_secs);
}

void aws_cbor_encode_bool(struct aws_cbor_encoder *encoder, bool value) {
    /* Major type 7 (simple), value 20 (false) and 21 (true) */
    uint8_t ctrl_value = value == true ? 21 : 20;
    ENCODE_THROUGH_LIBCBOR(1, encoder, ctrl_value, cbor_encode_ctrl);
}

void aws_cbor_encode_null(struct aws_cbor_encoder *encoder) {
    /* Major type 7 (simple), value 22 (null) */
    ENCODE_THROUGH_LIBCBOR(1, encoder, (uint8_t)22 /*null*/, cbor_encode_ctrl);
}

void aws_cbor_encode_undefine(struct aws_cbor_encoder *encoder) {
    /* Major type 7 (simple), value 23 (undefined) */
    ENCODE_THROUGH_LIBCBOR(1, encoder, (uint8_t)23 /*undefined*/, cbor_encode_ctrl);
}

void aws_cbor_encode_inf_start(struct aws_cbor_encoder *encoder, enum aws_cbor_element_type type) {
    /* All inf start takes 1 byte only */
    aws_byte_buf_reserve_dynamic(&encoder->encoded_buf, encoder->encoded_buf.len + 1);
    size_t encoded_len = 0;
    switch (type) {
        case AWS_CBOR_TYPE_INF_BYTESTRING:
            encoded_len = cbor_encode_indef_bytestring_start(
                encoder->encoded_buf.buffer + encoder->encoded_buf.len,
                encoder->encoded_buf.capacity - encoder->encoded_buf.len);
            break;
        case AWS_CBOR_TYPE_INF_STRING:
            encoded_len = cbor_encode_indef_string_start(
                encoder->encoded_buf.buffer + encoder->encoded_buf.len,
                encoder->encoded_buf.capacity - encoder->encoded_buf.len);
            break;
        case AWS_CBOR_TYPE_INF_ARRAY_START:
            encoded_len = cbor_encode_indef_array_start(
                encoder->encoded_buf.buffer + encoder->encoded_buf.len,
                encoder->encoded_buf.capacity - encoder->encoded_buf.len);
            break;
        case AWS_CBOR_TYPE_INF_MAP_START:
            encoded_len = cbor_encode_indef_map_start(
                encoder->encoded_buf.buffer + encoder->encoded_buf.len,
                encoder->encoded_buf.capacity - encoder->encoded_buf.len);
            break;

        default:
            break;
    }
    AWS_ASSERT(encoded_len == 1);
    encoder->encoded_buf.len += encoded_len;
}

void aws_cbor_encode_break(struct aws_cbor_encoder *encoder) {
    /* Major type 7 (simple), value 31 (break) */
    /* break takes 1 byte */
    /* Notes: cannot use cbor_encode_ctrl cause it will encode value 31 as 1 byte to follow the argument, instead of
     * argument directly.  */
    aws_byte_buf_reserve_dynamic(&encoder->encoded_buf, encoder->encoded_buf.len + 1);
    size_t encoded_len = cbor_encode_break(
        encoder->encoded_buf.buffer + encoder->encoded_buf.len,
        encoder->encoded_buf.capacity - encoder->encoded_buf.len);
    AWS_ASSERT(encoded_len == 1);
    encoder->encoded_buf.len += encoded_len;
}

void aws_cbor_encode_epoch_timestamp_ms(struct aws_cbor_encoder *encoder, int64_t epoch_time_ms) {
    aws_cbor_encode_tag(encoder, AWS_CBOR_TAG_EPOCH_TIME);
    aws_cbor_encode_double(encoder, (double)epoch_time_ms / 1000.0);
}
/* TODO: big number and big decimal */

/*******************************************************************************
 * DECODE
 ******************************************************************************/

struct aws_cbor_decoder_context {
    enum aws_cbor_element_type type;

    /* All the values only valid when the type is set to corresponding type. */
    uint64_t unsigned_val;
    uint64_t neg_val;
    double double_val;
    uint64_t tag_val;
    bool boolean_val;
    struct aws_byte_cursor str_val;
    struct aws_byte_cursor bytes_val;
    uint64_t map_start;
    uint64_t array_start;
};

struct aws_cbor_decoder {
    struct aws_allocator *allocator;

    struct aws_byte_cursor src;
    uint64_t bytes_decoded;

    struct aws_cbor_decoder_context cached_context;

    /* Error code during decoding. Fail the decoding process without recovering, */
    int error_code;
};

struct aws_cbor_decoder *aws_cbor_decoder_new(struct aws_allocator *allocator, struct aws_byte_cursor *src) {

    struct aws_cbor_decoder *decoder = aws_mem_calloc(allocator, 1, sizeof(struct aws_cbor_decoder));
    decoder->allocator = allocator;
    decoder->src = *src;
    decoder->cached_context.type = AWS_CBOR_TYPE_MAX;

    /* TODO: refcount */
    return decoder;
}

struct aws_cbor_decoder *aws_cbor_decoder_release(struct aws_cbor_decoder *decoder) {
    aws_mem_release(decoder->allocator, decoder);
    return NULL;
}

size_t aws_cbor_decoder_get_remaining_length(struct aws_cbor_decoder *decoder) {
    return decoder->src.len;
}

#define CHECK_CONTEXT(decoder)                                                                                         \
    do {                                                                                                               \
        if ((decoder)->cached_context.type != AWS_CBOR_TYPE_MAX) {                                                     \
            /* Still have cached context */                                                                            \
            (decoder)->error_code = AWS_ERROR_INVALID_STATE;                                                           \
            return;                                                                                                    \
        }                                                                                                              \
    } while (0)

#define LIBCBOR_VALUE_CALLBACK(field, callback_type, cbor_type)                                                        \
    static void s_##field##_callback(void *ctx, callback_type val) {                                                   \
        struct aws_cbor_decoder *decoder = ctx;                                                                        \
        CHECK_CONTEXT(decoder);                                                                                        \
        (decoder)->cached_context.field = val;                                                                         \
        (decoder)->cached_context.type = cbor_type;                                                                    \
    }

LIBCBOR_VALUE_CALLBACK(unsigned_val, uint64_t, AWS_CBOR_TYPE_UINT)
LIBCBOR_VALUE_CALLBACK(neg_val, uint64_t, AWS_CBOR_TYPE_NEGINT)
LIBCBOR_VALUE_CALLBACK(boolean_val, bool, AWS_CBOR_TYPE_BOOL)
LIBCBOR_VALUE_CALLBACK(double_val, double, AWS_CBOR_TYPE_DOUBLE)
LIBCBOR_VALUE_CALLBACK(map_start, uint64_t, AWS_CBOR_TYPE_MAP_START)
LIBCBOR_VALUE_CALLBACK(array_start, uint64_t, AWS_CBOR_TYPE_ARRAY_START)
LIBCBOR_VALUE_CALLBACK(tag_val, uint64_t, AWS_CBOR_TYPE_TAG)

static void s_uint8_callback(void *ctx, uint8_t data) {
    s_unsigned_val_callback(ctx, (uint64_t)data);
}

static void s_uint16_callback(void *ctx, uint16_t data) {
    s_unsigned_val_callback(ctx, (uint64_t)data);
}

static void s_uint32_callback(void *ctx, uint32_t data) {
    s_unsigned_val_callback(ctx, (uint64_t)data);
}

static void s_negint8_callback(void *ctx, uint8_t data) {
    s_neg_val_callback(ctx, (uint64_t)data);
}

static void s_negint16_callback(void *ctx, uint16_t data) {
    s_neg_val_callback(ctx, (uint64_t)data);
}

static void s_negint32_callback(void *ctx, uint32_t data) {
    s_neg_val_callback(ctx, (uint64_t)data);
}

static void s_float_callback(void *ctx, float data) {
    s_double_val_callback(ctx, (double)data);
}

static void s_bytes_callback(void *ctx, const unsigned char *cbor_data, uint64_t length) {
    struct aws_cbor_decoder *decoder = ctx;
    CHECK_CONTEXT(decoder);
    if (length > SIZE_MAX) {
        decoder->error_code = AWS_ERROR_OVERFLOW_DETECTED;
        return;
    }
    decoder->cached_context.type = AWS_CBOR_TYPE_BYTESTRING;
    decoder->cached_context.bytes_val.ptr = (uint8_t *)cbor_data;
    decoder->cached_context.bytes_val.len = (size_t)length;
}

static void s_str_callback(void *ctx, const unsigned char *cbor_data, uint64_t length) {
    struct aws_cbor_decoder *decoder = ctx;
    CHECK_CONTEXT(decoder);
    if (length > SIZE_MAX) {
        decoder->error_code = AWS_ERROR_OVERFLOW_DETECTED;
        return;
    }
    decoder->cached_context.type = AWS_CBOR_TYPE_STRING;
    decoder->cached_context.str_val.ptr = (uint8_t *)cbor_data;
    decoder->cached_context.str_val.len = (size_t)length;
}

#define LIBCBOR_SIMPLE_CALLBACK(field, cbor_type)                                                                      \
    static void s_##field##_callback(void *ctx) {                                                                      \
        struct aws_cbor_decoder *decoder = ctx;                                                                        \
        CHECK_CONTEXT(decoder);                                                                                        \
        (decoder)->cached_context.type = cbor_type;                                                                    \
    }

LIBCBOR_SIMPLE_CALLBACK(inf_bytes, AWS_CBOR_TYPE_INF_BYTESTRING)
LIBCBOR_SIMPLE_CALLBACK(inf_str, AWS_CBOR_TYPE_INF_STRING)
LIBCBOR_SIMPLE_CALLBACK(inf_array, AWS_CBOR_TYPE_INF_ARRAY_START)
LIBCBOR_SIMPLE_CALLBACK(inf_map, AWS_CBOR_TYPE_INF_MAP_START)

LIBCBOR_SIMPLE_CALLBACK(inf_break, AWS_CBOR_TYPE_BREAK)
LIBCBOR_SIMPLE_CALLBACK(undefined, AWS_CBOR_TYPE_UNDEFINE)
LIBCBOR_SIMPLE_CALLBACK(null, AWS_CBOR_TYPE_NULL)

static struct cbor_callbacks s_callbacks = {
    /** Unsigned int */
    .uint64 = s_unsigned_val_callback,
    /** Unsigned int */
    .uint32 = s_uint32_callback,
    /** Unsigned int */
    .uint16 = s_uint16_callback,
    /** Unsigned int */
    .uint8 = s_uint8_callback,

    /** Negative int */
    .negint64 = s_neg_val_callback,
    /** Negative int */
    .negint32 = s_negint32_callback,
    /** Negative int */
    .negint16 = s_negint16_callback,
    /** Negative int */
    .negint8 = s_negint8_callback,

    /** Indefinite byte string start */
    .byte_string_start = s_inf_bytes_callback,
    /** Definite byte string */
    .byte_string = s_bytes_callback,

    /** Definite string */
    .string = s_str_callback,
    /** Indefinite string start */
    .string_start = s_inf_str_callback,

    /** Definite array */
    .indef_array_start = s_inf_array_callback,
    /** Indefinite array */
    .array_start = s_array_start_callback,

    /** Definite map */
    .indef_map_start = s_inf_map_callback,
    /** Indefinite map */
    .map_start = s_map_start_callback,

    /** Tags */
    .tag = s_tag_val_callback,

    /** Half float */
    .float2 = s_float_callback,
    /** Single float */
    .float4 = s_float_callback,
    /** Double float */
    .float8 = s_double_val_callback,
    /** Undef */
    .undefined = s_undefined_callback,
    /** Null */
    .null = s_null_callback,
    /** Bool */
    .boolean = s_boolean_val_callback,

    /** Indefinite item break */
    .indef_break = s_inf_break_callback,
};

/**
 * decode the next element to the cached_content.
 */
int aws_cbor_decode_next_element(struct aws_cbor_decoder *decoder) {
    struct cbor_decoder_result result = cbor_stream_decode(decoder->src.ptr, decoder->src.len, &s_callbacks, decoder);
    switch (result.status) {
        case CBOR_DECODER_NEDATA:
            /* TODO: specific error code and log. */
            decoder->error_code = AWS_ERROR_INVALID_ARGUMENT;
            break;
        case CBOR_DECODER_ERROR:
            /* TODO: specific error code and log. */
            decoder->error_code = AWS_ERROR_INVALID_INDEX;
            break;
        default:
            break;
    }

    if (decoder->error_code) {
        /* Error happened during decoding */
        return aws_raise_error(decoder->error_code);
    }

    aws_byte_cursor_advance(&decoder->src, result.read);
    decoder->bytes_decoded += result.read;

    return AWS_OP_SUCCESS;
}

#define GET_NEXT_ITEM(field, out_type, expected_cbor_type)                                                             \
    /* NOLINTNEXTLINE(bugprone-macro-parentheses) */                                                                   \
    int aws_cbor_decode_get_next_##field(struct aws_cbor_decoder *decoder, out_type *out) {                            \
        if ((decoder)->error_code) {                                                                                   \
            /* Error happened during decoding */                                                                       \
            return aws_raise_error((decoder)->error_code);                                                             \
        }                                                                                                              \
        if ((decoder)->cached_context.type != AWS_CBOR_TYPE_MAX) {                                                     \
            /* There was a cached context, check if the cached one meets the expected. */                              \
            goto decode_done;                                                                                          \
        }                                                                                                              \
        if (aws_cbor_decode_next_element(decoder)) {                                                                   \
            return AWS_OP_ERR;                                                                                         \
        }                                                                                                              \
    decode_done:                                                                                                       \
        if ((decoder)->cached_context.type != (expected_cbor_type)) {                                                  \
            /* TODO: specific error code: UNEXPECTED_TYPE */                                                           \
            return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);                                                        \
        } else {                                                                                                       \
            /* Clear the cache as we give it out. */                                                                   \
            (decoder)->cached_context.type = AWS_CBOR_TYPE_MAX;                                                        \
            *out = (decoder)->cached_context.field;                                                                    \
        }                                                                                                              \
        return AWS_OP_SUCCESS;                                                                                         \
    }

GET_NEXT_ITEM(unsigned_val, uint64_t, AWS_CBOR_TYPE_UINT)
GET_NEXT_ITEM(neg_val, uint64_t, AWS_CBOR_TYPE_NEGINT)
GET_NEXT_ITEM(double_val, double, AWS_CBOR_TYPE_DOUBLE)
GET_NEXT_ITEM(boolean_val, bool, AWS_CBOR_TYPE_BOOL)
GET_NEXT_ITEM(str_val, struct aws_byte_cursor, AWS_CBOR_TYPE_STRING)
GET_NEXT_ITEM(bytes_val, struct aws_byte_cursor, AWS_CBOR_TYPE_BYTESTRING)
GET_NEXT_ITEM(map_start, uint64_t, AWS_CBOR_TYPE_MAP_START)
GET_NEXT_ITEM(array_start, uint64_t, AWS_CBOR_TYPE_ARRAY_START)
GET_NEXT_ITEM(tag_val, uint64_t, AWS_CBOR_TYPE_TAG)

int aws_cbor_decode_peek_type(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *out_type) {
    if (decoder->error_code) {
        /* Error happened during decoding */
        return aws_raise_error(decoder->error_code);
    }

    if (decoder->cached_context.type != AWS_CBOR_TYPE_MAX) {
        /* There was a cached context, return the type. */
        *out_type = decoder->cached_context.type;
        return AWS_OP_SUCCESS;
    }

    /* Decode */
    if (aws_cbor_decode_next_element(decoder)) {
        return AWS_OP_ERR;
    }
    *out_type = decoder->cached_context.type;
    return AWS_OP_SUCCESS;
}

int aws_cbor_decode_get_next_epoch_timestamp_ms_val(struct aws_cbor_decoder *decoder, int64_t *out) {
    if (decoder->error_code) {
        return aws_raise_error(decoder->error_code);
    }
    if (decoder->cached_context.type != AWS_CBOR_TYPE_MAX) {
        /* There was a cached context, check if the cached one meets the expected. */
        goto decode_tag_done;
    }
    if (aws_cbor_decode_next_element(decoder)) {
        return AWS_OP_ERR;
    }

decode_tag_done:

    if (decoder->cached_context.type != AWS_CBOR_TYPE_TAG ||
        decoder->cached_context.tag_val != AWS_CBOR_TAG_EPOCH_TIME) {
        /* TODO: specific error code: UNEXPECTED_TYPE */
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    /* Get the next element as the content */
    enum aws_cbor_element_type val_type = 0;
    /* Reset the cache for the tag val */
    decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
    int error = aws_cbor_decode_peek_type(decoder, &val_type);
    switch (val_type) {
        case AWS_CBOR_TYPE_UINT: {
            uint64_t timestamp_secs = 0;
            error |= aws_cbor_decode_get_next_unsigned_val(decoder, &timestamp_secs);
            if (error) {
                break;
            }
            uint64_t timestamp_ms = aws_mul_u64_saturating(timestamp_secs, 1000);
            if (timestamp_ms > INT64_MAX) {
                /* LOG */
                error = AWS_ERROR_OVERFLOW_DETECTED;
                break;
            }
            *out = (int64_t)timestamp_ms;
            break;
        }

        case AWS_CBOR_TYPE_NEGINT: {
            uint64_t timestamp_secs = 0;
            error |= aws_cbor_decode_get_next_neg_val(decoder, &timestamp_secs);
            if (error) {
                break;
            }
            uint64_t timestamp_ms = aws_mul_u64_saturating(timestamp_secs, 1000);
            if (timestamp_ms > INT64_MAX) {
                /* LOG */
                error = AWS_ERROR_OVERFLOW_DETECTED;
                break;
            }
            *out = (int64_t)timestamp_ms * -1LL;
            break;
        }

        case AWS_CBOR_TYPE_DOUBLE: {
            double timestamp_secs = 0;
            error |= aws_cbor_decode_get_next_double_val(decoder, &timestamp_secs);
            if (error) {
                break;
            }
            /* TODO: How to check overflow? */
            double ms_double = timestamp_secs * 1000.0;
            int64_t timestamp_ms = llround(ms_double);
            if (fetestexcept(FE_INVALID) || timestamp_ms > INT64_MAX) {
                /* LOG */
                error = AWS_ERROR_OVERFLOW_DETECTED;
                break;
            }
            *out = timestamp_ms;
            break;
        }
        default:
            /* MALFORMED */
            decoder->error_code = AWS_ERROR_MALFORMED_INPUT_STRING;
            error = aws_raise_error(AWS_ERROR_MALFORMED_INPUT_STRING);
            break;
    }
    if (error) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

int aws_cbor_decode_consume_next_data_item(struct aws_cbor_decoder *decoder) {

    if (decoder->cached_context.type == AWS_CBOR_TYPE_MAX) {
        /* There was no cache, decode the next item */
        if (aws_cbor_decode_next_element(decoder)) {
            return AWS_OP_ERR;
        }
    }
    switch (decoder->cached_context.type) {
        case AWS_CBOR_TYPE_TAG:
            /* Read the next data item */
            decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
            if (aws_cbor_decode_consume_next_data_item(decoder)) {
                return AWS_OP_ERR;
            }
            break;
        case AWS_CBOR_TYPE_MAP_START: {
            uint64_t num_map_item = decoder->cached_context.map_start;
            /* Reset type */
            decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
            for (uint64_t i = 0; i < num_map_item; i++) {
                /* Key */
                if (aws_cbor_decode_consume_next_data_item(decoder)) {
                    return AWS_OP_ERR;
                }
                /* Value */
                if (aws_cbor_decode_consume_next_data_item(decoder)) {
                    return AWS_OP_ERR;
                }
            }
            break;
        }
        case AWS_CBOR_TYPE_ARRAY_START: {
            uint64_t num_array_item = decoder->cached_context.array_start;
            /* Reset type */
            decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
            for (uint64_t i = 0; i < num_array_item; i++) {
                /* item */
                if (aws_cbor_decode_consume_next_data_item(decoder)) {
                    return AWS_OP_ERR;
                }
            }
            break;
        }
        case AWS_CBOR_TYPE_INF_BYTESTRING:
        case AWS_CBOR_TYPE_INF_STRING:
        case AWS_CBOR_TYPE_INF_ARRAY_START:
        case AWS_CBOR_TYPE_INF_MAP_START: {
            /* TODO: Error check for map, string and bytestring */
            enum aws_cbor_element_type next_type;
            /* Reset the cache for the tag val */
            decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
            if (aws_cbor_decode_peek_type(decoder, &next_type)) {
                return AWS_OP_ERR;
            }
            while (next_type != AWS_CBOR_TYPE_BREAK) {
                if (aws_cbor_decode_consume_next_data_item(decoder)) {
                    return AWS_OP_ERR;
                }
                if (aws_cbor_decode_peek_type(decoder, &next_type)) {
                    return AWS_OP_ERR;
                }
            }
            break;
        }

        default:
            break;
    }

    /* Done, just reset the cache */
    decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
    return AWS_OP_SUCCESS;
}

int aws_cbor_decode_consume_next_element(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *consumed_type) {
    enum aws_cbor_element_type out_type = 0;
    if (aws_cbor_decode_peek_type(decoder, &out_type)) {
        return AWS_OP_ERR;
    }
    if (consumed_type) {
        *consumed_type = out_type;
    }
    /* Reset the type to clear the cache. */
    decoder->cached_context.type = AWS_CBOR_TYPE_MAX;
    return AWS_OP_SUCCESS;
}
