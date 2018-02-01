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

static const char *hex_chars = "0123456789abcdef";

static const uint8_t base64_sentinal_value = 0xff;
static const char base64_encoding_table[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
static uint8_t base64_decoding_table[256];
static int8_t base64_decoding_table_init = 0;

static const uint8_t bytes_7 = 7 * 8;
static const uint8_t bytes_6 = 6 * 8;
static const uint8_t bytes_5 = 5 * 8;
static const uint8_t bytes_4 = 4 * 8;
static const uint8_t bytes_3 = 3 * 8;
static const uint8_t bytes_2 = 2 * 8;
static const uint8_t bytes_1 = 1 * 8;
static const uint8_t mask = 0xff;


int aws_hex_encode(const uint8_t *to_encode, size_t to_encode_len, char *output, size_t *output_size) {

    size_t encoded_len = (to_encode_len << 1) + 1;

    if(encoded_len <= to_encode_len) {
        return aws_raise_error(AWS_ERROR_OVERFLOW_DETECTED);
    }

    if (!output) {
        *output_size = encoded_len;
        return AWS_OP_SUCCESS;
    }

    if (*output_size < encoded_len) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    /* empty string should have output of "" */
    if(encoded_len == 1 && *to_encode == '\0') {
        *output_size = 1;
        *output = '\0';
    }

    size_t written = 0;
    for (size_t i = 0; i < to_encode_len; ++i) {

        output[written++] = hex_chars[to_encode[i] >> 4 & 0x0f];
        output[written++] = hex_chars[to_encode[i] & 0x0f];
    }

    output[written++] = '\0';
    *output_size = written;

    return AWS_OP_SUCCESS;
}

static uint8_t char_to_int(char character) {
    if (character >= 'a' && character <= 'f') {
        return (uint8_t)(10 + (character - 'a'));
    }

    if (character >= 'A' && character <= 'F') {
        return (uint8_t)(10 + (character - 'A'));
    }

    return (uint8_t)(character - '0');
}

int aws_hex_decode(const char *to_decode, size_t to_decode_len, uint8_t *output, size_t *output_size) {
    size_t decoded_length = (to_decode_len + 1) >> 1;

    if (!output) {
        *output_size = decoded_length;
        return AWS_OP_SUCCESS;
    }

    if (*output_size < decoded_length) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    size_t written = 0;

    size_t i = 0;

    //if the buffer isn't even, prepend a 0 to the buffer.
    if (to_decode_len & 0x01) {
        i = 1;
        output[written++] = char_to_int(to_decode[i]);
    }

    for (; i < to_decode_len; i += 2) {
        uint8_t value = char_to_int(to_decode[i]) << 4;
        value |= char_to_int(to_decode[i + 1]);
        output[written++] = value;
    }

    *output_size = written;

    return AWS_OP_SUCCESS;
}

static size_t calculate_base64_decoded_length(const char *input, size_t len) {
    if (len == 0) {
        return 0;
    }

    size_t padding = 0;

    if (len >= 2 && input[len - 1] == '=' && input[len - 2] == '=') { /*last two chars are = */
        padding = 2;
    }
    else if (input[len - 1] == '=') { /*last char is = */
        padding = 1;
    }

    return (len * 3 / 4 - padding);
}

static size_t calculate_base64_encoded_length(size_t buffer_len) {
    return 4 * ((buffer_len + 2) / 3) + 1; /* plus one for the NULL terminator */
}

int aws_base64_encode(const uint8_t *to_encode, size_t to_encode_len, char *output, size_t *output_size) {

    size_t encoded_length = calculate_base64_encoded_length(to_encode_len);
    if(!output) {
        *output_size = encoded_length;
        return AWS_OP_SUCCESS;
    }

    if(*output_size < encoded_length) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    *output_size = encoded_length;

    size_t buffer_length = to_encode_len;
    size_t block_count = (buffer_length + 2) / 3;
    size_t remainder_count = (buffer_length % 3);
    size_t str_index = 0;

    for(size_t i = 0; i < to_encode_len; i += 3 )
    {
        uint32_t block = to_encode[ i ];

        block <<= 8;
        if (i + 1 < buffer_length)
        {
            block = block | to_encode[ i + 1 ];
        }

        block <<= 8;
        if (i + 2 < to_encode_len)
        {
            block = block | to_encode[ i + 2 ];
        }

        output[str_index++] = base64_encoding_table[(block >> 18) & 0x3F];
        output[str_index++] = base64_encoding_table[(block >> 12) & 0x3F];
        output[str_index++] = base64_encoding_table[(block >> 6) & 0x3F];
        output[str_index++] = base64_encoding_table[block & 0x3F];
    }

    if(remainder_count > 0)
    {
        output[block_count * 4 - 1] = '=';
        if(remainder_count == 1)
        {
            output[block_count * 4 - 2] = '=';
        }
    }

    return AWS_OP_SUCCESS;
}

static void init_decoding_table() {
    if(!base64_decoding_table_init) {
        for(size_t i = 0; i < (sizeof(base64_encoding_table) / sizeof(char)); ++i)
        {
            size_t index = (size_t)base64_encoding_table[i];
            base64_decoding_table[index] = (uint8_t)i;
        }

        base64_decoding_table[(size_t)'='] = base64_sentinal_value;
        base64_decoding_table_init = 1;
    }
}

int aws_base64_decode(const char *to_decode, size_t to_decode_len, uint8_t *output, size_t *output_size) {
    size_t decoded_length = calculate_base64_decoded_length(to_decode, to_decode_len);

    if(!output) {
        *output_size = decoded_length;
        return AWS_OP_SUCCESS;
    }

    init_decoding_table();

    if (*output_size < decoded_length) {
        return aws_raise_error(AWS_ERROR_INVALID_BUFFER_SIZE);
    }

    *output_size = decoded_length;

    size_t block_count = to_decode_len / 4;
    size_t string_index = 0;

    for(size_t i = 0; i < block_count; ++i)
    {
        uint32_t value1 = base64_decoding_table[(size_t)to_decode[string_index++]];
        uint32_t value2 = base64_decoding_table[(size_t)to_decode[string_index++]];
        uint32_t value3 = base64_decoding_table[(size_t)to_decode[string_index++]];
        uint32_t value4 = base64_decoding_table[(size_t)to_decode[string_index++]];

        size_t buffer_index = i * 3;
        output[buffer_index++] = (uint8_t)((value1 << 2) | ((value2 >> 4) & 0x03));
        if(value3 != base64_sentinal_value)
        {
            output[buffer_index++] = (uint8_t)(((value2 << 4) & 0xF0) | ((value3 >> 2) & 0x0F));
            if(value4 != base64_sentinal_value)
            {
                output[buffer_index] = (uint8_t)((value3 & 0x03) << 6 | value4);
            }
        }
    }

    return AWS_OP_SUCCESS;
}

uint8_t *aws_add_uint64_to_buffer(uint8_t *buffer, uint64_t value) {
    buffer[0] = (uint8_t)(value >> bytes_7) & mask;
    buffer[1] = (uint8_t)(value >> bytes_6) & mask;
    buffer[2] = (uint8_t)(value >> bytes_5) & mask;
    buffer[3] = (uint8_t)(value >> bytes_4) & mask;
    buffer[4] = (uint8_t)(value >> bytes_3) & mask;
    buffer[5] = (uint8_t)(value >> bytes_2) & mask;
    buffer[6] = (uint8_t)(value >> bytes_1) & mask;
    buffer[7] = (uint8_t)(value)& mask;

    return buffer + sizeof(value);
}

uint64_t aws_uint64_from_buffer(const uint8_t *buffer) {
    uint64_t value = 0;
    value |= (uint64_t)buffer[0] << bytes_7;
    value |= (uint64_t)buffer[1] << bytes_6;
    value |= (uint64_t)buffer[2] << bytes_5;
    value |= (uint64_t)buffer[3] << bytes_4;
    value |= (uint64_t)buffer[4] << bytes_3;
    value |= (uint64_t)buffer[5] << bytes_2;
    value |= (uint64_t)buffer[6] << bytes_1;
    value |= buffer[7];

    return value;
}

uint8_t *aws_add_uint32_to_buffer(uint8_t *buffer, uint32_t value) {
    buffer[0] = (uint8_t)(value >> bytes_3) & mask;
    buffer[1] = (uint8_t)(value >> bytes_2) & mask;
    buffer[2] = (uint8_t)(value >> bytes_1) & mask;
    buffer[3] = (uint8_t)(value)& mask;

    return buffer + 4;
}

uint32_t aws_uint32_from_buffer(const uint8_t *buffer) {
    uint32_t value = 0;
    value |= (uint32_t)buffer[0] << bytes_3;
    value |= (uint32_t)buffer[1] << bytes_2;
    value |= (uint32_t)buffer[2] << bytes_1;
    value |= buffer[3];

    return value;
}

uint8_t * aws_add_uint24_to_buffer(uint8_t *buffer, uint32_t value) {
    buffer[0] = (uint8_t)(value >> bytes_2) & mask;
    buffer[1] = (uint8_t)(value >> bytes_1) & mask;
    buffer[2] = (uint8_t)(value)& mask;

    return buffer + 3;
}

uint32_t aws_uint24_from_buffer(const uint8_t *buffer) {
    uint32_t value = 0;

    value |= (uint32_t)buffer[0] << bytes_2;
    value |= (uint32_t)buffer[1] << bytes_1;
    value |= buffer[2];

    return value;
}

uint8_t *aws_add_uint16_to_buffer(uint8_t *buffer, uint16_t value) {
    buffer[0] = (uint8_t)(value >> bytes_1) & mask;
    buffer[1] = (uint8_t)(value)& mask;

    return buffer + 2;
}

uint16_t aws_uint16_from_buffer(const uint8_t *buffer) {
    uint16_t value = 0;
    value |= buffer[0];
    value <<= bytes_1;
    value |= buffer[1];

    return value;
}
