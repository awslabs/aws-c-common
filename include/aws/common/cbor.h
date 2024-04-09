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

    AWS_CBOR_TYPE_TAG,

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

/**
 * The common tags, refer to RFC8949 section 3.4
 * Expected value type followed by the tag:
 * AWS_CBOR_TAG_STANDARD_TIME - AWS_CBOR_TYPE_STRING
 * AWS_CBOR_TAG_EPOCH_TIME - AWS_CBOR_TYPE_UINT/AWS_CBOR_TYPE_NEGINT/AWS_CBOR_TYPE_DOUBLE
 * AWS_CBOR_TAG_UNSIGNED_BIGNUM - AWS_CBOR_TYPE_BYTESTRING
 * AWS_CBOR_TAG_NEGATIVE_BIGNUM - AWS_CBOR_TYPE_BYTESTRING
 * AWS_CBOR_TAG_DECIMAL_FRACTION - AWS_CBOR_TYPE_ARRAY_START/AWS_CBOR_TYPE_INF_ARRAY_START
 * AWS_CBOR_TAG_BIGFLOAT - AWS_CBOR_TYPE_ARRAY_START/AWS_CBOR_TYPE_INF_ARRAY_START
 **/
enum aws_cbor_tags {
    AWS_CBOR_TAG_STANDARD_TIME = 0,
    AWS_CBOR_TAG_EPOCH_TIME = 1,
    AWS_CBOR_TAG_UNSIGNED_BIGNUM = 2,
    AWS_CBOR_TAG_NEGATIVE_BIGNUM = 3,
    AWS_CBOR_TAG_DECIMAL_FRACTION = 4,
    AWS_CBOR_TAG_BIGFLOAT = 5,
    /* All the remain tags are unclassified */
    AWS_CBOR_TAG_UNCLASSIFIED,
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
 * @brief Encode a double value to "smallest possible", but will not be encoded into half-precision float, as it's not
 * well supported cross languages. To be more specific, it will be encoded into integer/negative/float (Order with
 * priority) when the conversation will not cause precision loss.
 *
 * TODO: the double and float math is very tricky. And there is undefined behavior if we just type cast.
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

AWS_COMMON_API
void aws_cbor_encode_tag(struct aws_cbor_encoder *encoder, uint64_t tag_number);

AWS_COMMON_API
void aws_cbor_encode_null(struct aws_cbor_encoder *encoder);

AWS_COMMON_API
void aws_cbor_encode_undefine(struct aws_cbor_encoder *encoder);

AWS_COMMON_API
void aws_cbor_encode_bool(struct aws_cbor_encoder *encoder, bool value);

/**
 * @brief Encode inf start, supported type is:
 *  AWS_CBOR_TYPE_INF_BYTESTRING
 *  AWS_CBOR_TYPE_INF_STRING
 *  AWS_CBOR_TYPE_INF_ARRAY_START
 *  AWS_CBOR_TYPE_INF_MAP_START
 * All other type will result in error.
 *
 * Notes: It's user's responsibility to track the break to
 * close the corresponding inf_star
 *
 * @param encoder
 * @param type
 */
AWS_COMMON_API
void aws_cbor_encode_inf_start(struct aws_cbor_encoder *encoder, enum aws_cbor_element_type type);

/* Encode the break for inf collections. Notes: no error checking, it's user's responsibility to track the break to
 * close the corresponding inf_start */
AWS_COMMON_API
void aws_cbor_encode_break(struct aws_cbor_encoder *encoder);
/* TODO: bignum/bigfloat */

/**
 * @brief Helper to encode an epoch timestamp on ms, equivelent to:
 *  aws_cbor_encode_tag(encoder, AWS_CBOR_TAG_EPOCH_TIME);
 *  aws_cbor_encode_double(encoder, (double)epoch_time_ms/1000.0);
 *
 * @param encoder
 * @param epoch_time_ms
 */
AWS_COMMON_API
void aws_cbor_encode_epoch_timestamp_ms(struct aws_cbor_encoder *encoder, int64_t epoch_time_ms);

/*******************************************************************************
 * DECODE
 ******************************************************************************/

AWS_COMMON_API
struct aws_cbor_decoder *aws_cbor_decoder_new(struct aws_allocator *allocator, struct aws_byte_cursor *src);

AWS_COMMON_API
struct aws_cbor_decoder *aws_cbor_decoder_release(struct aws_cbor_decoder *decoder);

/**
 * @brief  Get the length of the remaining data. Once the data was decoded, it will consume the data, and result in
 * decrease of the remaining length.
 *
 * @param decoder
 * @return The length remaining
 */
AWS_COMMON_API
size_t aws_cbor_decoder_get_remaining_length(struct aws_cbor_decoder *decoder);

/**
 * @brief Decode the next element and store it in the decoder cache if there was no element cached.
 * If there was element cached, just return the type of the cached element.
 *
 * @param src
 * @param out_type
 * @return int
 */
AWS_COMMON_API
int aws_cbor_decode_peek_type(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *out_type);

/**
 * @brief Consume the next data item, includes all the content within the data item.
 *
 * @param src The src to parse data from
 * @return AWS_OP_SUCCESS successfully consumed the next data item, otherwise AWS_OP_ERR.
 */
/* TODO: do we want to track the consumed size??? Decoder handles it already. */
AWS_COMMON_API
int aws_cbor_decode_consume_next_data_item(struct aws_cbor_decoder *decoder);

/**
 * @brief Consume the next element, without the content followed by the element.
 *
 * @param decoder The decoder to parse data from
 * @param consumed_type Optional, get the type of the consumed element.
 * @return AWS_OP_SUCCESS successfully consumed the next element, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_consume_next_element(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *consumed_type);

/**
 * @brief Get the next element based on the type. If the next element doesn't match the expected type. Error will be
 * raised. If the next element already been cached, it will consume the cached item when no error was returned.
 *
 * @param decoder
 * @param out
 * @return AWS_OP_SUCCESS successfully consumed the next element and get the result, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_unsigned_val(struct aws_cbor_decoder *decoder, uint64_t *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_neg_val(struct aws_cbor_decoder *decoder, uint64_t *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_double_val(struct aws_cbor_decoder *decoder, double *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_boolean_val(struct aws_cbor_decoder *decoder, bool *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_str_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_bytes_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);

/**
 * @brief
 *
 * @param decoder
 * @param out_size
 * @return AWS_COMMON_API
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_map_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);

AWS_COMMON_API
int aws_cbor_decode_get_next_array_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);

AWS_COMMON_API
int aws_cbor_decode_get_next_tag_val(struct aws_cbor_decoder *decoder, uint64_t *out_tag_number);

/**
 * @brief Helper to get the next tag element and the value followed. If the value is float/double, the value will be
 * truncated to fit millisecond precision
 *
 * @param decoder
 * @param out
 * @return int
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_epoch_timestamp_ms_val(struct aws_cbor_decoder *decoder, int64_t *out);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif // AWS_COMMON_CBOR_H
