#ifndef AWS_COMMON_ENCODING_H
#define AWS_COMMON_ENCODING_H

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

#include <aws/common/common.h>
#include <stdint.h>
#include <memory.h>

#ifdef _WIN32
#include <winsock2.h>
#else
#include <netinet/in.h>
#endif /*_WIN32 */

#ifdef __cplusplus
extern "C" {
#endif

/*
 * computes the length necessary to store the result of aws_hex_encode(). returns -1 on failure, and 0 on success.
 * encoded_length will be set on success.
 */
AWS_COMMON_API int aws_compute_hex_encoded_len(size_t to_encode_len, size_t *encoded_length);

/*
 * Base 16 (hex) encodes the contents of to_encode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_hex_encode(const uint8_t *restrict to_encode, size_t to_encode_len, char *restrict output, size_t output_size);

/*
 * computes the length necessary to store the result of aws_hex_decode(). returns -1 on failure, and 0 on success.
 * decoded_len will be set on success.
 */
AWS_COMMON_API int aws_compute_hex_decoded_len(size_t to_decode_len, size_t *decoded_len);

/*
 * Base 16 (hex) decodes the contents of to_decode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_hex_decode(const char *restrict to_decode, size_t to_decode_len, uint8_t *restrict output, size_t output_size);

/*
 * Computes the length necessary to store the output of aws_base64_encode call. returns -1 on failure, and 0 on success.
 * encoded_length will be set on success.
 */
AWS_COMMON_API int aws_compute_base64_encoded_len(size_t to_encode_len, size_t *encoded_len);

/*
 * Base 64 encodes the contents of to_encode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_base64_encode(const uint8_t *restrict to_encode, size_t to_encode_len, char *restrict output, size_t output_size);

/*
 * Computes the length necessary to store the output of aws_base64_decode call. returns -1 on failure, and 0 on success.
 * decoded_len will be set on success.
 */
AWS_COMMON_API int aws_compute_base64_decoded_len(const char *input, size_t len, size_t *decoded_len);
/*
 * Base 64 decodes the contents of to_decode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_base64_decode(const char *restrict to_decode, size_t to_decode_len, uint8_t *restrict output, size_t output_size);

#ifdef __cplusplus
}
#endif

/* Add a 64 bit unsigned integer to the buffer, ensuring network - byte order
 * Assumes the buffer size is at least 8 bytes.
 */
static inline void aws_write_u64(uint8_t *buffer, uint64_t value) {

    uint32_t low = htonl((uint32_t)value);
    uint32_t high = htonl((uint32_t)(value >> 32));
    memcpy((void *)buffer, (void *)&high, sizeof(high));
    memcpy((void *)(buffer + sizeof(high)), (void *)&low, sizeof(low));
}

/*
 * Extracts a 64 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order. Assumes buffer size is at least 8 bytes.
 */
static inline uint64_t aws_read_u64(const uint8_t *buffer) {
    uint64_t value = 0;

    uint32_t low = 0;
    uint32_t high = 0;
    memcpy((void *)&high, (void *)buffer, sizeof(high));
    memcpy((void *)&low, (void *)(buffer + sizeof(high)), sizeof(low));

    value = (uint64_t)ntohl(high) << 32;
    value |= (uint64_t)ntohl(low);

    return value;
}

/* Add a 32 bit unsigned integer to the buffer, ensuring network - byte order
 * Assumes the buffer size is at least 4 bytes.
 */
static inline void aws_write_u32(uint8_t *buffer, uint32_t value) {
    uint32_t be_value = htonl(value);

    memcpy((void *)buffer, (void *)&be_value, sizeof(be_value));
}

/*
 * Extracts a 32 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order. Assumes the buffer size is at least 4 bytes.
 */
static inline uint32_t aws_read_u32(const uint8_t *buffer) {
    uint32_t value = 0;
    memcpy((void *)&value, (void *)buffer, sizeof(value));

    return ntohl(value);
}

/* Add a 24 bit unsigned integer to the buffer, ensuring network - byte order
 * return the new position in the buffer for the next operation.
 * Note, since this uses uint32_t for storage, the 3 least significant bytes will be used.
 * Assumes buffer is at least 3 bytes long.
 */
static inline void aws_write_u24(uint8_t *buffer, uint32_t value) {
    uint32_t be_value = htonl(value);
    memcpy((void *)buffer, (void *)((uint8_t *)&be_value + 1), sizeof(be_value) - 1);
}

/*
 * Extracts a 24 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order. Assumes buffer is at least 3 bytes long.
 */
static inline uint32_t aws_read_u24(const uint8_t *buffer) {
    uint32_t value = 0;
    memcpy((void *)((uint8_t *)&value + 1), (void *)buffer, sizeof(value) - 1);

    return ntohl(value);
}

/* Add a 16 bit unsigned integer to the buffer, ensuring network-byte order
 * return the new position in the buffer for the next operation.
 * Assumes buffer is at least 2 bytes long.
 */
static inline void aws_write_u16(uint8_t *buffer, uint16_t value) {
    uint16_t be_value = htons(value);

    memcpy((void *)buffer, (void *)&be_value, sizeof(be_value));
}

/*
 * Extracts a 16 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order. Assumes buffer is at least 2 bytes long.
 */
static inline uint16_t aws_read_u16(const uint8_t *buffer) {
    uint16_t value = 0;
    memcpy((void *)&value, (void *)buffer, sizeof(value));

    return ntohs(value);
}

#endif /*AWS_COMMON_ENCODING_H*/
