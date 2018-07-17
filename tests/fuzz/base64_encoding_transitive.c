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

#include <assert.h>

int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {

    struct aws_allocator *alloc = aws_default_allocator();

    size_t output_size = 0;
    int result = aws_base64_compute_encoded_len(size, &output_size);
    assert(result == AWS_OP_SUCCESS);

    struct aws_byte_buf to_encode = aws_byte_buf_from_array(data, size);

    struct aws_byte_buf encode_allocation;
    result = aws_byte_buf_init(alloc, &encode_allocation, output_size + 2);
    assert(result == AWS_OP_SUCCESS);
    memset(encode_allocation.buffer, 0xdd, encode_allocation.capacity);
    struct aws_byte_buf encode_output = aws_byte_buf_from_array(encode_allocation.buffer + 1, output_size);
    encode_output.len = 0;

    result = aws_base64_encode(&to_encode, &encode_output);
    assert(result == AWS_OP_SUCCESS);
    assert(*encode_allocation.buffer == 0xdd);
    assert(*(encode_allocation.buffer + output_size + 1) == 0xdd);
    --encode_output.len; /* Remove null terminator */

    result = aws_base64_compute_decoded_len((const char *)encode_output.buffer, output_size - 1, &output_size);
    assert(result == AWS_OP_SUCCESS);
    assert(output_size == size);

    struct aws_byte_buf decode_allocation;
    result = aws_byte_buf_init(alloc, &decode_allocation, output_size + 2);
    assert(result == AWS_OP_SUCCESS);
    memset(decode_allocation.buffer, 0xdd, decode_allocation.capacity);
    struct aws_byte_buf decode_output = aws_byte_buf_from_array(decode_allocation.buffer + 1, output_size);
    decode_output.len = 0;

    result = aws_base64_decode(&encode_output, &decode_output);
    assert(result == AWS_OP_SUCCESS);

    assert(*decode_allocation.buffer == 0xdd);
    assert(*(decode_allocation.buffer + output_size + 1) == 0xdd);

    assert(output_size == decode_output.len);
    assert(memcmp(decode_output.buffer, data, size) == 0);

    aws_byte_buf_clean_up(&encode_allocation);
    aws_byte_buf_clean_up(&decode_allocation);

    return 0;
}
