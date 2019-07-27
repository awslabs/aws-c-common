/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#define DEST_TYPE uint32_t
#define BYTE_WIDTH 4
#define BYTE_CURSOR_READ aws_byte_cursor_read_be32
#define AWS_NTOH aws_ntoh32

#include <proof_helpers/aws_byte_cursor_read_common.h>

void aws_byte_cursor_read_be32_harness() {
    aws_byte_cursor_read_common_harness();
}
