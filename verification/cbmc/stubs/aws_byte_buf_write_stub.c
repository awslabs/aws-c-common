/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/byte_order.h>
#include <aws/common/common.h>
#include <string.h>

/**
 * Stub for aws_byte_buf_write.
 * Has the same behaviour as the actual function except it doesn't actually write the bytes.
 * In order to use this function safely, the user must check that the byte_buf bytes are not actually
 * used by the function under test.
 * TODO: Once CBMC supports proper havocing, should havoc the bytes to get full soundness.
 *
 * On success, returns true and updates the buffer length accordingly.
 * If there is insufficient space in the buffer, returns false, leaving the
 * buffer unchanged.
 */
bool aws_byte_buf_write(struct aws_byte_buf *AWS_RESTRICT buf, const uint8_t *AWS_RESTRICT src, size_t len) {
    AWS_PRECONDITION(aws_byte_buf_is_valid(buf));
    AWS_PRECONDITION(AWS_MEM_IS_WRITABLE(src, len), "Input array [src] must be readable up to [len] bytes.");

    if (buf->len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || buf->len + len > buf->capacity) {
        AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
        return false;
    }

    /* memcpy(buf->buffer + buf->len, src, len); */
    buf->len += len;

    AWS_POSTCONDITION(aws_byte_buf_is_valid(buf));
    return true;
}
