/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define DEST_TYPE uint32_t
#define BYTE_WIDTH 4
#define BYTE_CURSOR_READ aws_byte_cursor_read_be32
#define AWS_NTOH aws_ntoh32

#include <proof_helpers/aws_byte_cursor_read_common.h>

void aws_byte_cursor_read_be32_harness() {
    aws_byte_cursor_read_common_harness();
}
