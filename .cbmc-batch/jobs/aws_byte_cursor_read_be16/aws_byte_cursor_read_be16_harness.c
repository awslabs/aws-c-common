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

#define DEST_TYPE uint16_t
#define BYTE_WIDTH 2
#define BYTE_CURSOR_READ aws_byte_cursor_read_be16
#define AWS_NTOH aws_ntoh16

#include <proof_helpers/aws_byte_cursor_read_common.h>

void aws_byte_cursor_read_be16_harness() {
    aws_byte_cursor_read_common_harness();
}
