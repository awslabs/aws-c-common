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

#ifdef __cplusplus
extern "C" {
#endif

/*
 * Base 16 (hex) encodes the contents of to_encode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_hex_encode(const uint8_t *to_encode, size_t to_encode_len, char *output, size_t *output_size);

/*
 * Base 16 (hex) decodes the contents of to_decode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_hex_decode(const char *to_decode, size_t to_decode_len, uint8_t *output, size_t *output_size);

/*
 * Base 64 encodes the contents of to_encode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_base64_encode(const uint8_t *to_encode, size_t to_encode_len, char *output, size_t *output_size);

/*
 * Base 64 decodes the contents of to_decode and stores the result in output.
 * If output is NULL, output_size will be set to what the output_size should be.
 */
AWS_COMMON_API int aws_base64_decode(const char *to_decode, size_t to_decode_len, uint8_t *output, size_t *output_size);

/*Add a 64 bit unsigned integer to the buffer, ensuring network - byte order
 * return the new position in the buffer for the next operation.
 */
AWS_COMMON_API uint8_t *aws_add_uint64_to_buffer(uint8_t *buffer, uint64_t value);

/*
 * Extracts a 64 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order
 */
AWS_COMMON_API uint64_t aws_uint64_from_buffer(const uint8_t *buffer);

/*Add a 32 bit unsigned integer to the buffer, ensuring network - byte order
    * return the new position in the buffer for the next operation. */
AWS_COMMON_API uint8_t *aws_add_uint32_to_buffer(uint8_t *buffer, uint32_t value);

/*
 * Extracts a 32 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order
 */
AWS_COMMON_API uint32_t aws_uint32_from_buffer(const uint8_t *buffer);

/*Add a 24 bit unsigned integer to the buffer, ensuring network - byte order
    * return the new position in the buffer for the next operation.
    * Note, since this uses uint32_t for storage, the 3 least significant bytes will be used.*/
AWS_COMMON_API uint8_t *aws_add_uint24_to_buffer(uint8_t *buffer, uint32_t value);

/*
 * Extracts a 24 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order
 */
AWS_COMMON_API uint32_t aws_uint24_from_buffer(const uint8_t *buffer);

/* Add a 16 bit unsigned integer to the buffer, ensuring network-byte order
* return the new position in the buffer for the next operation. */
AWS_COMMON_API uint8_t *aws_add_uint16_to_buffer(uint8_t *buffer, uint16_t value);

/*
 * Extracts a 16 bit unsigned integer from buffer. Ensures conversion from network byte order to
 * host byte order
 */
AWS_COMMON_API uint16_t aws_uint16_from_buffer(const uint8_t *buffer);

#ifdef __cplusplus
}
#endif

#endif /*AWS_COMMON_ENCODING_H*/
