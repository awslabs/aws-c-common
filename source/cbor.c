#include "external/libcbor/cbor.h"
#include <aws/common/cbor.h>

#include <aws/common/private/json_impl.h>
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

#define ENCODE_THROUGH_LIBCBOR(length_to_reserve, to, value, fn)                                                       \
    do {                                                                                                               \
        aws_byte_buf_reserve_dynamic(to, to->len + length_to_reserve);                                                 \
        size_t encoded_len = fn(value, to->buffer + to->len, to->capacity - to->len);                                  \
        AWS_ASSERT(encoded_len != 0);                                                                                  \
        to->len += encoded_len;                                                                                        \
    } while (false)

void aws_cbor_encode_uint(struct aws_byte_buf *to, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, to, value, cbor_encode_uint);
}

void aws_cbor_encode_negint(struct aws_byte_buf *to, uint64_t value) {
    ENCODE_THROUGH_LIBCBOR(9, to, value, cbor_encode_negint);
}

void aws_cbor_encode_bool(struct aws_byte_buf *to, bool value) {
    /* Major type 7 (simple), value 20 (false) and 21 (true) */
    uint8_t ctrl_value = value == true ? 21 : 20;
    ENCODE_THROUGH_LIBCBOR(1, to, ctrl_value, cbor_encode_ctrl);
}

void aws_cbor_encode_single_float(struct aws_byte_buf *to, float value) {
    ENCODE_THROUGH_LIBCBOR(5, to, value, cbor_encode_single);
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
void aws_cbor_encode_double(struct aws_byte_buf *to, double value) {
    if (isnan(value) || isinf(value)) {
        /* For special value: NAN/INFINITY, type cast to float and encode into single float. */
        aws_cbor_encode_single_float(to, (float)value);
        return;
    }

    /* TODO: try to convert to uint/negint, if cannot, try to convert to float */
    ENCODE_THROUGH_LIBCBOR(9, to, value, cbor_encode_double);
}

void aws_cbor_encode_map_start(struct aws_byte_buf *to, size_t map_size) {
    ENCODE_THROUGH_LIBCBOR(9, to, map_size, cbor_encode_map_start);
}

void aws_cbor_encode_array_start(struct aws_byte_buf *to, size_t map_size) {
    ENCODE_THROUGH_LIBCBOR(9, to, map_size, cbor_encode_array_start);
}

void aws_cbor_encode_bytes(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    /* Reserve the bytes for the byte string start cbor item and the actual bytes */
    /* Encode the first cbor item for byte string */
    ENCODE_THROUGH_LIBCBOR(9 + from->len, to, from->len, cbor_encode_bytestring_start);
    /* Append the actual bytes to follow the cbor item */
    aws_byte_buf_append(to, from);
}

void aws_cbor_encode_string(struct aws_byte_buf *to, const struct aws_byte_cursor *from) {
    /* Reserve the bytes for the byte string start cbor item and the actual string */
    /* Encode the first cbor item for byte string */
    ENCODE_THROUGH_LIBCBOR(9 + from->len, to, from->len, cbor_encode_string_start);
    /* Append the actual string to follow the cbor item */
    aws_byte_buf_append(to, from);
}

void aws_cbor_encode_epoch_timestamp_secs(struct aws_byte_buf *to, double epoch_time_secs) {
    /* Encode the tag cbor item with tag value 1, as Epoch-based date/time */
    ENCODE_THROUGH_LIBCBOR(1, to, 1, cbor_encode_tag);
    /* Encode the tag content item as unsigned or negative integer (major types 0 and 1) or a floating-point number
     * (major type 7 with additional information 25, 26, or 27) */
    aws_cbor_encode_double(to, epoch_time_secs);
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

struct aws_cbor_item *aws_cbor_load(struct aws_byte_cursor *from, struct aws_allocator *allocator) {
    struct cbor_load_result result = {0};
    struct cbor_item_t *lib_cbor_item = cbor_load(from->ptr, from->len, &result);
    switch (result.error.code) {
        case CBOR_ERR_NONE:
            /* Succeed, the read bytes are?? */
            goto succeed;

        default:
            /* Freak out for now */
            AWS_ASSERT(false);
            break;
    }
succeed:
    struct aws_cbor_item *item = aws_mem_acquire(allocator, sizeof(struct aws_cbor_item));
    item->allocator = allocator;
    item->lib_cbor_item = lib_cbor_item;
    /* Move the cursor to how many we already read. */
    aws_byte_cursor_advance(from, result.read);
    return item;
}

// struct aws_cbor_type
