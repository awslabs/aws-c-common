#ifndef AWS_COMMON_CBOR_H
#define AWS_COMMON_CBOR_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/common.h>

AWS_PUSH_SANE_WARNING_LEVEL
AWS_EXTERN_C_BEGIN

enum aws_cbor_element_type {
    AWS_CBOR_TYPE_UINT,
    AWS_CBOR_TYPE_NEGINT,
    AWS_CBOR_TYPE_DOUBLE,
    AWS_CBOR_TYPE_BYTESTRING,
    AWS_CBOR_TYPE_STRING,

    AWS_CBOR_TYPE_ARRAY_START,
    AWS_CBOR_TYPE_MAP_START,
    AWS_CBOR_TYPE_EPOCH_TIMESTAMP_SECS,
    AWS_CBOR_TYPE_UNCLASSIFIED_TAG,

    AWS_CBOR_TYPE_NULL,
    AWS_CBOR_TYPE_UNDEFINE,
    AWS_CBOR_TYPE_BOOL,
    AWS_CBOR_TYPE_BREAK,

    AWS_CBOR_TYPE_INF_BYTESTRING,
    AWS_CBOR_TYPE_INF_STRING,
    AWS_CBOR_TYPE_INF_ARRAY_START,
    AWS_CBOR_TYPE_INF_MAP_START,

    AWS_CBOR_TYPE_MAX,
};

struct aws_cbor_encoder;
struct aws_cbor_decoder;

/*******************************************************************************
 * ENCODE
 ******************************************************************************/

AWS_COMMON_API
struct aws_cbor_encoder *aws_cbor_encoder_new(struct aws_allocator *allocator, size_t init_buffer_size);

AWS_COMMON_API
struct aws_cbor_encoder *aws_cbor_encoder_release(struct aws_cbor_encoder *encoder);

AWS_COMMON_API
struct aws_byte_cursor aws_cbor_encoder_get_encoded_data(struct aws_cbor_encoder *encoder);

AWS_COMMON_API
void aws_cbor_encoder_clear_encoded_data(struct aws_cbor_encoder *encoder);

AWS_COMMON_API
void aws_cbor_encode_uint(struct aws_cbor_encoder *encoder, uint64_t value);
AWS_COMMON_API
void aws_cbor_encode_negint(struct aws_cbor_encoder *encoder, uint64_t value);

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
AWS_COMMON_API
void aws_cbor_encode_double(struct aws_cbor_encoder *encoder, double value);

AWS_COMMON_API
void aws_cbor_encode_bytes(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from);

AWS_COMMON_API
void aws_cbor_encode_string(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from);

AWS_COMMON_API
void aws_cbor_encode_array_start(struct aws_cbor_encoder *encoder, size_t number_entries);

AWS_COMMON_API
void aws_cbor_encode_map_start(struct aws_cbor_encoder *encoder, size_t number_entries);

void aws_cbor_encode_epoch_timestamp_secs(struct aws_cbor_encoder *encoder, double epoch_time_secs);

void aws_cbor_encode_null(struct aws_cbor_encoder *encoder);
void aws_cbor_encode_bool(struct aws_cbor_encoder *encoder, bool value);

/* TODO: bignum/bigfloat */

/*******************************************************************************
 * DECODE
 ******************************************************************************/

struct aws_cbor_decoder *aws_cbor_decoder_new(struct aws_allocator *allocator, struct aws_byte_cursor *src);

/**
 * @brief Decode the next element and store it in the decoder cache if there was no element cached.
 * If there was element cached, just return the type of the cached element.
 *
 * @param src
 * @param out_type
 * @return int
 */
int aws_cbor_decode_peek_type(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *out_type);

/**
 * @brief Consume the next data item, includes all the content within the data item.
 *
 * @param src The src to parse data from
 * @return AWS_OP_SUCCESS successfully consumed the next data item, otherwise AWS_OP_ERR.
 */
/* TODO: do we want to track the consumed size??? Decoder handles it already. */
int aws_cbor_decode_consume_next_data_item(struct aws_cbor_decoder *decoder);

/**
 * @brief Get the next element based on the type. If the next element doesn't match the expected type. Error will be
 * raised. If the next element already been cached, it will consume the cached item when no error was returned.
 *
 * @param decoder
 * @param out
 * @return int
 */
int aws_cbor_decode_get_next_unsigned_val(struct aws_cbor_decoder *decoder, uint64_t *out);
int aws_cbor_decode_get_next_neg_val(struct aws_cbor_decoder *decoder, uint64_t *out);
int aws_cbor_decode_get_next_double_val(struct aws_cbor_decoder *decoder, double *out);
int aws_cbor_decode_get_next_boolean_val(struct aws_cbor_decoder *decoder, bool *out);
int aws_cbor_decode_get_next_str_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);
int aws_cbor_decode_get_next_bytes_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);
int aws_cbor_decode_get_next_timestamp_secs_val(struct aws_cbor_decoder *decoder, double *out);
int aws_cbor_decode_get_next_map_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);
int aws_cbor_decode_get_next_array_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);
int aws_cbor_decode_get_next_unclassified_tag_val(struct aws_cbor_decoder *decoder, uint64_t *out_tag_number);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif // AWS_COMMON_CBOR_H
