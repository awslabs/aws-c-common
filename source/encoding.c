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

#include <aws/common/encoding.h>
#include <ctype.h>
#include <assert.h>

static const char *hex_chars = "0123456789abcdef";

static const uint8_t base64_sentinal_value = 0xff;
static const char base64_encoding_table[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/* in this table, 0xDD is an invalid decoded value, if you have to do byte counting for any reason, there's 16 bytes
 * per row. */
/* clang-format off */
static uint8_t base64_decoding_table[256] = {
            64, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 62, 0xDD, 0xDD, 0xDD, 63,
            52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 0xDD, 0xDD, 0xDD, 255, 0xDD, 0xDD,
            0xDD, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
            15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
            41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
            0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD };
/* clang-format on */

int aws_hex_compute_encoded_len(size_t to_encode_len, size_t *encoded_length) {
    assert(encoded_length);

    size_t temp = (to_encode_len << 1) + 1;

    if (AWS_UNLIKELY(temp < to_encode_len)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    *encoded_length = temp;

    return AWS_OP_SUCCESS;
}

int aws_hex_encode(const uint8_t *AWS_RESTRICT to_encode, size_t to_encode_len, char *AWS_RESTRICT output, size_t output_size) {
    assert(to_encode);
    assert(output);

    size_t encoded_len = 0;

    if (AWS_UNLIKELY(aws_hex_compute_encoded_len(to_encode_len, &encoded_len))) {
        return AWS_OP_ERR;
    }

    if (AWS_UNLIKELY(output_size < encoded_len)) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    size_t written = 0;
    for (size_t i = 0; i < to_encode_len; ++i) {

        output[written++] = hex_chars[to_encode[i] >> 4 & 0x0f];
        output[written++] = hex_chars[to_encode[i] & 0x0f];
    }

    output[written] = '\0';

    return AWS_OP_SUCCESS;
}

static int hex_decode_char_to_int(char character, uint8_t *int_val) {
    if (character >= 'a' && character <= 'f') {
        *int_val = (uint8_t)(10 + (character - 'a'));
        return 0;
    }

    else if (character >= 'A' && character <= 'F') {
        *int_val = (uint8_t)(10 + (character - 'A'));
        return 0;
    }

    else if (character >= '0' && character <= '9') {
        *int_val = (uint8_t)(character - '0');
        return 0;
    }

    return AWS_OP_ERR;
}

int aws_hex_compute_decoded_len(size_t to_decode_len, size_t *decoded_len) {
    assert(decoded_len);

    size_t temp = (to_decode_len + 1);

    if (AWS_UNLIKELY(temp < to_decode_len)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    *decoded_len = temp >> 1;
    return AWS_OP_SUCCESS;
}

int aws_hex_decode(const char *AWS_RESTRICT to_decode, size_t to_decode_len, uint8_t *AWS_RESTRICT output, size_t output_size) {
    assert(to_decode);
    assert(output);

    size_t decoded_length = 0;

    if (AWS_UNLIKELY(aws_hex_compute_decoded_len(to_decode_len, &decoded_length))) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    if (AWS_UNLIKELY(output_size < decoded_length)) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    size_t written = 0;
    size_t i = 0;
    uint8_t high_value = 0;
    uint8_t low_value = 0;

    /* if the buffer isn't even, prepend a 0 to the buffer. */
    if (AWS_UNLIKELY(to_decode_len & 0x01)) {
        i = 1;
        if (hex_decode_char_to_int(to_decode[0], &low_value)) {
            return aws_raise_error(AWS_ERROR_INVALID_HEX_STR);
        }

        output[written++] = low_value;
    }

    for (; i < to_decode_len; i += 2) {
        if (AWS_UNLIKELY(hex_decode_char_to_int(to_decode[i], &high_value) ||
                         hex_decode_char_to_int(to_decode[i + 1], &low_value))) {
            return aws_raise_error(AWS_ERROR_INVALID_HEX_STR);
        }

        uint8_t value = high_value << 4;
        value |= low_value;
        output[written++] = value;
    }

    return AWS_OP_SUCCESS;
}

int aws_base64_compute_encoded_len(size_t to_encode_len, size_t *encoded_len) {
    assert(encoded_len);

    size_t tmp = to_encode_len + 2;

    if (AWS_UNLIKELY(tmp < to_encode_len)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    tmp /= 3;
    size_t overflow_check = tmp;
    tmp = 4 * tmp + 1; /* plus one for the NULL terminator */

    if (AWS_UNLIKELY(tmp < overflow_check)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    *encoded_len = tmp;

    return AWS_OP_SUCCESS;
}

int aws_base64_compute_decoded_len(const char *input, size_t len, size_t *decoded_len) {
    assert(input);
    assert(decoded_len);

    if (len == 0) {
        *decoded_len = 0;
        return AWS_OP_SUCCESS;
    }

    if (AWS_UNLIKELY(len & 0x03)) {
        return aws_raise_error(AWS_ERROR_INVALID_BASE64_STR);
    }

    size_t padding = 0;

    if (len >= 2 && input[len - 1] == '=' && input[len - 2] == '=') { /*last two chars are = */
        padding = 2;
    } else if (input[len - 1] == '=') { /*last char is = */
        padding = 1;
    }

    size_t tmp = len * 3;

    if (AWS_UNLIKELY(tmp < len)) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    *decoded_len = (tmp / 4 - padding);
    return AWS_OP_SUCCESS;
}

int aws_base64_encode(const uint8_t *AWS_RESTRICT to_encode, size_t to_encode_len, char *AWS_RESTRICT output, size_t output_size) {
    assert(to_encode);
    assert(output);

    size_t encoded_length = 0;
    if (AWS_UNLIKELY(aws_base64_compute_encoded_len(to_encode_len, &encoded_length))) {
        return AWS_OP_ERR;
    }

    if (AWS_UNLIKELY(output_size < encoded_length)) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    size_t buffer_length = to_encode_len;
    size_t block_count = (buffer_length + 2) / 3;
    size_t remainder_count = (buffer_length % 3);
    size_t str_index = 0;

    for (size_t i = 0; i < to_encode_len; i += 3) {
        uint32_t block = to_encode[i];

        block <<= 8;
        if (AWS_LIKELY(i + 1 < buffer_length)) {
            block = block | to_encode[i + 1];
        }

        block <<= 8;
        if (AWS_LIKELY(i + 2 < to_encode_len)) {
            block = block | to_encode[i + 2];
        }

        output[str_index++] = base64_encoding_table[(block >> 18) & 0x3F];
        output[str_index++] = base64_encoding_table[(block >> 12) & 0x3F];
        output[str_index++] = base64_encoding_table[(block >> 6) & 0x3F];
        output[str_index++] = base64_encoding_table[block & 0x3F];
    }

    if (remainder_count > 0) {
        output[block_count * 4 - 1] = '=';
        if (remainder_count == 1) {
            output[block_count * 4 - 2] = '=';
        }
    }

    /* it's a string add the null terminator. */
    output[encoded_length - 1] = 0;

    return AWS_OP_SUCCESS;
}

static inline int base64_get_decoded_value(char to_decode, uint8_t *value, int8_t allow_sentinal) {
    uint8_t decode_value = base64_decoding_table[(size_t)to_decode];
    if (decode_value != 0xDD && (decode_value != base64_sentinal_value || allow_sentinal)) {
        *value = decode_value;
        return AWS_OP_SUCCESS;
    }

    return AWS_OP_ERR;
}

int aws_base64_decode(const char *AWS_RESTRICT to_decode, size_t to_decode_len, uint8_t *AWS_RESTRICT output, size_t output_size) {
    size_t decoded_length = 0;

    if (AWS_UNLIKELY(aws_base64_compute_decoded_len(to_decode, to_decode_len, &decoded_length))) {
        return AWS_OP_ERR;
    }

    if (output_size < decoded_length) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    int64_t block_count = (int)to_decode_len / 4;
    size_t string_index = 0;
    uint8_t value1 = 0, value2 = 0, value3 = 0, value4 = 0;
    int64_t buffer_index = 0;

    for (int32_t i = 0; i < block_count - 1; ++i) {
        if (AWS_UNLIKELY(base64_get_decoded_value(to_decode[string_index++], &value1, 0) ||
                         base64_get_decoded_value(to_decode[string_index++], &value2, 0) ||
                         base64_get_decoded_value(to_decode[string_index++], &value3, 0) ||
                         base64_get_decoded_value(to_decode[string_index++], &value4, 0))) {
            return aws_raise_error(AWS_ERROR_INVALID_BASE64_STR);
        }

        buffer_index = i * 3;
        output[buffer_index++] = (uint8_t)((value1 << 2) | ((value2 >> 4) & 0x03));
        output[buffer_index++] = (uint8_t)(((value2 << 4) & 0xF0) | ((value3 >> 2) & 0x0F));
        output[buffer_index] = (uint8_t)((value3 & 0x03) << 6 | value4);
    }

    buffer_index = (block_count - 1) * 3;

    if (buffer_index >= 0) {
        if (base64_get_decoded_value(to_decode[string_index++], &value1, 0) ||
            base64_get_decoded_value(to_decode[string_index++], &value2, 0) ||
            base64_get_decoded_value(to_decode[string_index++], &value3, 1) ||
            base64_get_decoded_value(to_decode[string_index], &value4, 1)) {
            return aws_raise_error(AWS_ERROR_INVALID_BASE64_STR);
        }

        output[buffer_index++] = (uint8_t)((value1 << 2) | ((value2 >> 4) & 0x03));

        if (value3 != base64_sentinal_value) {
            output[buffer_index++] = (uint8_t)(((value2 << 4) & 0xF0) | ((value3 >> 2) & 0x0F));
            if (value4 != base64_sentinal_value) {
                output[buffer_index] = (uint8_t)((value3 & 0x03) << 6 | value4);
            }
        }
    }

    return AWS_OP_SUCCESS;
}
