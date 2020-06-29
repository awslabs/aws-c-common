/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define DEST_TYPE uint16_t
#define BYTE_WIDTH 2
#define BYTE_CURSOR_READ aws_byte_cursor_read_be16
#define AWS_NTOH aws_ntoh16

#include <proof_helpers/aws_byte_cursor_read_common.h>

void aws_byte_cursor_read_be16_harness() {
    aws_byte_cursor_read_common_harness();
}
