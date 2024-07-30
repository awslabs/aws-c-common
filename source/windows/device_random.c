/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/device_random.h>

#include <aws/common/byte_buf.h>

#include <windows.h>

#include <bcrypt.h>

int aws_device_random_buffer(struct aws_byte_buf *output) {
    return aws_device_random_buffer_append(output, output->capacity - output->len);
}

int aws_device_random_buffer_append(struct aws_byte_buf *output, size_t n) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(output));

    size_t space_available = output->capacity - output->len;
    if (space_available < n) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(output));
        return aws_raise_error(AWS_ERROR_SHORT_BUFFER);
    }

    size_t original_len = output->len;

    /* BCryptGenRandom() takes 32bit length, but we accept size_t,
     * so work in chunks if necessary. */
    while (n > 0) {
        uint32_t capped_n = (uint32_t)aws_min_size(n, UINT32_MAX);

        NTSTATUS status =
            BCryptGenRandom(NULL, output->buffer + output->len, capped_n, BCRYPT_USE_SYSTEM_PREFERRED_RNG);

        if (!BCRYPT_SUCCESS(status)) {
            output->len = original_len;
            AWS_POSTCONDITION(aws_byte_buf_is_valid(output));
            return aws_raise_error(AWS_ERROR_RANDOM_GEN_FAILED);
        }

        output->len += capped_n;
        n -= capped_n;
    }

    AWS_POSTCONDITION(aws_byte_buf_is_valid(output));
    return AWS_OP_SUCCESS;
}
