#include "external/libcbor/cbor.h"
#include <aws/common/cbor.h>

#include <aws/common/array_list.h>
#include <aws/common/private/json_impl.h>
#include <aws/common/ref_count.h>
#include <math.h>

static struct aws_allocator *s_aws_cbor_module_allocator = NULL;
static bool s_aws_cbor_module_initialized = false;

static void *s_cbor_mem_malloc(size_t size) {
    return aws_mem_acquire(s_aws_cbor_module_allocator, size);
}

static void *s_cbor_mem_realloc(void *ptr, size_t old_size, size_t new_size) {
    void *return_ptr = ptr;
    /* aws_mem_realloc cannot fail now. */
    aws_mem_realloc(s_aws_cbor_module_allocator, &return_ptr, old_size, new_size);
    return return_ptr;
}

static void s_cbor_mem_free(void *ptr) {
    aws_mem_release(s_aws_cbor_module_allocator, ptr);
}

void aws_cbor_module_init(struct aws_allocator *allocator) {
    if (!s_aws_cbor_module_initialized) {
        s_aws_cbor_module_allocator = allocator;
        cbor_set_allocs(s_cbor_mem_malloc, s_cbor_mem_realloc, s_cbor_mem_free);
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

struct aws_cbor_encoder *aws_cbor_encoder_new(struct aws_allocator *allocator, size_t init_buffer_size) {}
struct aws_byte_cursor aws_cbor_encoder_get_encoded_data(struct aws_cbor_encoder *encoder);
void aws_cbor_encoder_clear_encoded_data(struct aws_cbor_encoder *encoder);

#define ENCODE_THROUGH_LIBCBOR(length_to_reserve, encoder, value, fn)                                                  \
    do {                                                                                                               \
        aws_byte_buf_reserve_dynamic(&encoder->encoded_buf, encoder->encoded_buf.len + length_to_reserve);             \
        size_t encoded_len =                                                                                           \
            fn(value,                                                                                                  \
               encoder->encoded_buf.buffer + encoder->encoded_buf.len,                                                 \
               encoder->encoded_buf.capacity - encoder->encoded_buf.len);                                              \
        AWS_ASSERT(encoded_len != 0);                                                                                  \
        encoder->encoded_buf.len += encoded_len;                                                                       \
    } while (false)

void aws_cbor_encode_uint(struct aws_cbor_encoder *encoder, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_uint);
}

void aws_cbor_encode_negint(struct aws_cbor_encoder *encoder, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_negint);
}

void aws_cbor_encode_bool(struct aws_cbor_encoder *encoder, bool value) {
    /* Major type 7 (simple), value 20 (false) and 21 (true) */
    uint8_t ctrl_value = value == true ? 21 : 20;
    ENCODE_THROUGH_LIBCBOR(1, encoder, ctrl_value, cbor_encode_ctrl);
}

void aws_cbor_encode_single_float(struct aws_cbor_encoder *encoder, float value) {
    ENCODE_THROUGH_LIBCBOR(5, encoder, value, cbor_encode_single);
}

/**
 * @brief Encode a double value to "smallest possible", but will not be encoded into half-precision float, as it's
 not
 * well supported cross languages. To be more specific, it will be encoded into integer/negative/float (Order with
 * priority) when the conversation will not cause precision loss.
 *
 * @param to
 * @param value
 * @param dynamic_expand
 * @return int
 */
void aws_cbor_encode_double(struct aws_cbor_encoder *encoder, double value) {
    if (isnan(value) || isinf(value)) {
        /* For special value: NAN/INFINITY, type cast to float and encode into single float. */
        aws_cbor_encode_single_float(encoder, (float)value);
        return;
    }

    /* TODO: try to convert to uint/negint, if cannot, try to convert to float */
    ENCODE_THROUGH_LIBCBOR(9, encoder, value, cbor_encode_double);
}

void aws_cbor_encode_map_start(struct aws_cbor_encoder *encoder, size_t map_size) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, map_size, cbor_encode_map_start);
}

void aws_cbor_encode_array_start(struct aws_cbor_encoder *encoder, size_t map_size) {
    ENCODE_THROUGH_LIBCBOR(9, encoder, map_size, cbor_encode_array_start);
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

/* TODO: big number and big decimal */

/*******************************************************************************
 * DECODE
 ******************************************************************************/

struct aws_cbor_item {
    struct aws_allocator *allocator;
    struct cbor_item_t *lib_cbor_item;
};

enum aws_cbor_type {
    AWS_CBOR_TYPE_UINT,
    AWS_CBOR_TYPE_NEGINT,
    AWS_CBOR_TYPE_BYTESTRING,
    AWS_CBOR_TYPE_STRING,
    AWS_CBOR_TYPE_ARRAY,
    AWS_CBOR_TYPE_MAP,
    AWS_CBOR_TYPE_EPOCH_TIMESTAMP,
    AWS_CBOR_TYPE_TAG,
    AWS_CBOR_TYPE_DOUBLE,
    AWS_CBOR_TYPE_FLOAT_CTRL,
};

struct aws_cbor_decoder {
    struct aws_allocator *allocator;

    /* To support adding more chunks to parse */
    struct aws_array_list src_list;
};

struct aws_cbor_decoder *aws_cbor_decoder_new(struct aws_allocator *allocator, struct aws_byte_cursor *src) {}

/**
 * @brief Add a chunk for decoder to parse.
 *  Note: The chunk has to be added in the right order. The decoder won't copy the data from src, it's caller's
 * responsibilty to keep the src data outlive the decoding process.
 *
 * @param src
 */
void aws_cbor_decoder_add_chunk(struct aws_byte_cursor *src) {}

/**
 * Invoked when next cbor element is a uint type.
 * Return AWS_OP_SUCCESS to move forward.
 * Return AWS_OP_ERR and raise an error for failure from the callback.
 */
typedef int(aws_cbor_decode_on_uint_fn)(uint64_t data, void *user_data);

struct aws_cbor_decode_options {
    bool skip_consume_data;
    void *user_data;

    /* callbacks for each type */
    aws_cbor_decode_on_uint_fn *on_uint;
};

int aws_cbor_decode_next_element(struct aws_byte_cursor *src, struct aws_cbor_decode_options *options) {
    return AWS_OP_SUCCESS;
}

/**
 * @brief Consume the next data item, includes all the content within the data item, from the src.
 *
 * @param src The src to parse data from
 * @return AWS_OP_SUCCESS successfully consumed the next data item, otherwise AWS_OP_ERR.
 */
int aws_cbor_decode_consume_next_data_item(struct aws_byte_cursor *src) {
    return AWS_OP_SUCCESS;
}

/**
 * @brief Don't consume any data.
 *
 * @param src
 * @param out_type
 * @return int
 */
int aws_cbor_decode_peek_type(struct aws_byte_cursor *src, int *out_type) {}
