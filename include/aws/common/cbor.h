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

/**
 * The element types use by peek type.
 * An extension for cbor major type in RFC8949 section 3.1
 * Major type 0 - AWS_CBOR_TYPE_UINT
 * Major type 1 - AWS_CBOR_TYPE_NEGINT
 * Major type 2 - AWS_CBOR_TYPE_BYTESTRING/AWS_CBOR_TYPE_INF_BYTESTRING_START
 * Major type 3 - AWS_CBOR_TYPE_STRING/AWS_CBOR_TYPE_INF_STRING_START
 * Major type 4 - AWS_CBOR_TYPE_ARRAY_START/AWS_CBOR_TYPE_INF_ARRAY_START
 * Major type 5 - AWS_CBOR_TYPE_MAP_START/AWS_CBOR_TYPE_INF_MAP_START
 * Major type 6 - AWS_CBOR_TYPE_TAG
 * Major type 7
 *  - 20/21 - AWS_CBOR_TYPE_BOOL
 *  - 22 - AWS_CBOR_TYPE_NULL
 *  - 23 - AWS_CBOR_TYPE_UNDEFINE
 *  - 25/26/27 - AWS_CBOR_TYPE_DOUBLE
 *  - 31 - AWS_CBOR_TYPE_BREAK
 *  - result of value not supported.
 */
enum aws_cbor_element_type {
    AWS_CBOR_TYPE_UINT,
    AWS_CBOR_TYPE_NEGINT,
    AWS_CBOR_TYPE_DOUBLE,
    AWS_CBOR_TYPE_BYTESTRING,
    AWS_CBOR_TYPE_STRING,

    AWS_CBOR_TYPE_ARRAY_START,
    AWS_CBOR_TYPE_MAP_START,

    AWS_CBOR_TYPE_TAG,

    AWS_CBOR_TYPE_BOOL,
    AWS_CBOR_TYPE_NULL,
    AWS_CBOR_TYPE_UNDEFINE,
    AWS_CBOR_TYPE_BREAK,

    AWS_CBOR_TYPE_INF_BYTESTRING_START,
    AWS_CBOR_TYPE_INF_STRING_START,
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

    /* Unclassified doesn't match to any tags. */
    AWS_CBOR_TAG_UNCLASSIFIED,
};

struct aws_cbor_encoder;
struct aws_cbor_decoder;

/*******************************************************************************
 * ENCODE
 ******************************************************************************/

/**
 * @brief Create a new cbor encoder. Creating a encoder with a temporay buffer.
 * Every aws_cbor_encode_* will encode directly into the buffer to follow the encoded data.
 *
 * @param allocator
 * @param init_buffer_size The initial size of the temporary buffer, which will grow as needed.
 * @return aws_cbor_encoder
 */
AWS_COMMON_API
struct aws_cbor_encoder *aws_cbor_encoder_new(struct aws_allocator *allocator, size_t init_buffer_size);

AWS_COMMON_API
struct aws_cbor_encoder *aws_cbor_encoder_release(struct aws_cbor_encoder *encoder);

/**
 * @brief Get the current encoded buffer from encoder.
 *
 * @param encoder
 * @return struct aws_byte_cursor from the encoder buffer.
 */
AWS_COMMON_API
struct aws_byte_cursor aws_cbor_encoder_get_encoded_data(struct aws_cbor_encoder *encoder);

/**
 * @brief Clear the current encoded buffer from encoder.
 *
 * @param encoder
 */
AWS_COMMON_API
void aws_cbor_encoder_clear_encoded_data(struct aws_cbor_encoder *encoder);

/**
 * @brief Encode a AWS_CBOR_TYPE_UINT value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1
 *
 * @param encoder
 * @param value value to encode.
 */
AWS_COMMON_API
void aws_cbor_encode_uint(struct aws_cbor_encoder *encoder, uint64_t value);

/**
 * @brief Encode a AWS_CBOR_TYPE_NEGINT value to "smallest possible" in encoder's buffer.
 * It represents (-1 - value).
 *  Referring to RFC8949 section 4.2.1
 *
 *
 * @param encoder
 * @param value The argument to encode to negative integer, which is (-1 - expected_val)
 */
AWS_COMMON_API
void aws_cbor_encode_negint(struct aws_cbor_encoder *encoder, uint64_t value);

/**
 * @brief Encode a AWS_CBOR_TYPE_DOUBLE value to "smallest possible", but will not be encoded into half-precision float,
 * as it's not well supported cross languages.
 *
 * To be more specific, it will be encoded into integer/negative/float
 * (Order with priority) when the conversation will not cause precision loss.
 *
 * @param encoder
 * @param value value to encode.
 */
AWS_COMMON_API
void aws_cbor_encode_double(struct aws_cbor_encoder *encoder, double value);

/**
 * @brief Encode a AWS_CBOR_TYPE_BYTESTRING value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1, the length of "from" will be encoded first and then the value of "from" will
 * be followed.
 *
 * @param encoder
 * @param from value to encode.
 */
AWS_COMMON_API
void aws_cbor_encode_bytes(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from);

/**
 * @brief Encode a AWS_CBOR_TYPE_STRING value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1, the length of "from" will be encoded first and then the value of "from" will
 * be followed.
 *
 * @param encoder
 * @param from value to encode.
 */
AWS_COMMON_API
void aws_cbor_encode_string(struct aws_cbor_encoder *encoder, const struct aws_byte_cursor *from);

/**
 * @brief Encode a AWS_CBOR_TYPE_ARRAY_START value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1
 *  The "number_entries" is the cbor data items should be followed as the content of the array.
 * Notes: it's user's responsibility to keep the integrity of the array to be encoded.
 *
 * @param encoder
 * @param number_entries The number of data item in array.
 */
AWS_COMMON_API
void aws_cbor_encode_array_start(struct aws_cbor_encoder *encoder, size_t number_entries);

/**
 * @brief Encode a AWS_CBOR_TYPE_MAP_START value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1
 *  The "number_entries" is the number of pair of cbor data items as key and value should be followed as the content of
 * the map.
 *
 * Notes: it's user's responsibility to keep the integrity of the map to be encoded.
 *
 * @param encoder
 * @param number_entries The number of data item in map.
 */
AWS_COMMON_API
void aws_cbor_encode_map_start(struct aws_cbor_encoder *encoder, size_t number_entries);

/**
 * @brief Encode a AWS_CBOR_TYPE_TAG value to "smallest possible" in encoder's buffer.
 *  Referring to RFC8949 section 4.2.1
 * The following cbor data item will be the content of the tagged value.
 * Notes: it's user's responsibility to keep the integrity of the tagged value to follow the RFC8949 section 3.4
 *
 * @param encoder
 * @param tag_number The tag value to encode.
 */
AWS_COMMON_API
void aws_cbor_encode_tag(struct aws_cbor_encoder *encoder, uint64_t tag_number);

/**
 * @brief Encode a simple value AWS_CBOR_TYPE_NULL
 *
 * @param encoder
 */
AWS_COMMON_API
void aws_cbor_encode_null(struct aws_cbor_encoder *encoder);

/**
 * @brief Encode a simple value AWS_CBOR_TYPE_UNDEFINE
 *
 * @param encoder
 */
AWS_COMMON_API
void aws_cbor_encode_undefine(struct aws_cbor_encoder *encoder);

/**
 * @brief Encode a simple value AWS_CBOR_TYPE_BOOL
 *
 * @param encoder
 */
AWS_COMMON_API
void aws_cbor_encode_bool(struct aws_cbor_encoder *encoder, bool value);

/**
 * @brief Encode a simple value AWS_CBOR_TYPE_BREAK
 *
 * Notes: no error checking, it's user's responsibility to track the break
 * to close the corresponding inf_start
 */
AWS_COMMON_API
void aws_cbor_encode_break(struct aws_cbor_encoder *encoder);

/**
 * @brief Encode inf start, supported type is:
 *  AWS_CBOR_TYPE_INF_BYTESTRING_START
 *  AWS_CBOR_TYPE_INF_STRING_START
 *  AWS_CBOR_TYPE_INF_ARRAY_START
 *  AWS_CBOR_TYPE_INF_MAP_START
 * All other type will result in error.
 *
 * Notes: It's user's responsibility to track and add the break to
 * close the corresponding inf_start
 *
 * @param encoder
 * @param type
 */
AWS_COMMON_API
int aws_cbor_encode_inf_start(struct aws_cbor_encoder *encoder, enum aws_cbor_element_type type);

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

/**
 * @brief Create a cbor decoder to take src to decode.
 * The typical usage of decoder will be:
 * - If the next element type only accept what expected, `aws_cbor_decode_get_next_*`
 * - If the next element type accept different type, invoke `aws_cbor_decode_peek_type` first, then based on the type to
 * invoke corresponding `aws_cbor_decode_get_next_*`
 * - If the next element type doesn't have corrsponding value, specifically: AWS_CBOR_TYPE_NULL, AWS_CBOR_TYPE_UNDEFINE,
 * AWS_CBOR_TYPE_INF_*_START, AWS_CBOR_TYPE_BREAK, call `aws_cbor_decode_consume_next_element` to consume it and
 * continues for further decoding.
 * - To ignore the next data item (the element and the content of it), `aws_cbor_decode_consume_next_data_item`
 *
 * Note: it's caller's responsibilty to keep the src outlive the decoder.
 *
 * @param allocator
 * @param src   The src data to decode from.
 * @return decoder
 */
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
 * @param decoder
 * @param out_type
 * @return AWS_OP_SUCCESS if succeed, AWS_OP_ERR for any decoding error and corresponding error code will be raised.
 */
AWS_COMMON_API
int aws_cbor_decode_peek_type(struct aws_cbor_decoder *decoder, enum aws_cbor_element_type *out_type);

/**
 * @brief Consume the next data item, includes all the content within the data item.
 * Notes: this function will not ensure the data item is well-formed.
 *
 * @param src The src to parse data from
 * @return AWS_OP_SUCCESS successfully consumed the next data item, otherwise AWS_OP_ERR.
 */
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
 * Specifically:
 *  AWS_CBOR_TYPE_UINT - aws_cbor_decode_get_next_unsigned_val
 *  AWS_CBOR_TYPE_NEGINT - aws_cbor_decode_get_next_neg_val, it represents (-1 - *out)
 *  AWS_CBOR_TYPE_DOUBLE - aws_cbor_decode_get_next_double_val
 *  AWS_CBOR_TYPE_BYTESTRING - aws_cbor_decode_get_next_bytes_val
 *  AWS_CBOR_TYPE_STRING - aws_cbor_decode_get_next_str_val
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
int aws_cbor_decode_get_next_bytes_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);
AWS_COMMON_API
int aws_cbor_decode_get_next_str_val(struct aws_cbor_decoder *decoder, struct aws_byte_cursor *out);

/**
 * @brief Get the next AWS_CBOR_TYPE_ARRAY_START element. Only consume the AWS_CBOR_TYPE_ARRAY_START element and set the
 * size of array to *out_size, not the content of the array. The next *out_size cbor data items will be the content of
 * the array for a valid cbor data,
 *
 * @param decoder
 * @param out_size store the size of array if succeed.
 * @return AWS_OP_SUCCESS successfully consumed the next element and get the result, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_array_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);

/**
 * @brief Get the next AWS_CBOR_TYPE_MAP_START element. Only consume the AWS_CBOR_TYPE_MAP_START element and set the
 * size of array to *out_size, not the content of the map. The next *out_size pair of cbor data items as key and value
 * will be the content of the array for a valid cbor data,
 *
 * @param decoder
 * @param out_size store the size of map if succeed.
 * @return AWS_OP_SUCCESS successfully consumed the next element and get the result, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_map_start(struct aws_cbor_decoder *decoder, uint64_t *out_size);

/**
 * @brief Get the next AWS_CBOR_TYPE_TAG element. Only consume the AWS_CBOR_TYPE_TAG element and set the
 * tag value to *out_tag_val, not the content of the tagged. The next cbor data item will be the content of the tagged
 * value for a valid cbor data.
 *
 * @param decoder
 * @param out_size store the size of map if succeed.
 * @return AWS_OP_SUCCESS successfully consumed the next element and get the result, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_tag_val(struct aws_cbor_decoder *decoder, uint64_t *out_tag_val);

/**
 * @brief Helper to get the next tag element and the value followed. If the value is float/double, the value will be
 * truncated to fit millisecond precision.
 *
 * @param decoder
 * @param out
 * @return AWS_OP_SUCCESS successfully consumed the next element and get the result, otherwise AWS_OP_ERR.
 */
AWS_COMMON_API
int aws_cbor_decode_get_next_epoch_timestamp_ms_val(struct aws_cbor_decoder *decoder, int64_t *out);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif // AWS_COMMON_CBOR_H
