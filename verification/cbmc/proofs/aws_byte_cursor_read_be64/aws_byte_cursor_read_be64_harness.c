/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define DEST_TYPE uint64_t
#define BYTE_WIDTH 8
#define BYTE_CURSOR_READ aws_byte_cursor_read_be64
#define AWS_NTOH aws_ntoh64

#include <proof_helpers/aws_byte_cursor_read_common.h>

void aws_byte_cursor_read_be64_harness() {
    aws_byte_cursor_read_common_harness();
}
