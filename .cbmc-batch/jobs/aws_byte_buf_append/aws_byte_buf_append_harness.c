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

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_append_harness() {
    size_t len1 = nondet_size_t();
    __CPROVER_assume(len1 <= MAX_BUF_LEN);
    size_t len2 = nondet_size_t();

    /* Need arbitrary buf that is "correct enough" */
    struct aws_byte_buf *to;
    ASSUME_VALID_MEMORY(to);
    ASSUME_VALID_MEMORY_COUNT(to->buffer, len1);
    to->capacity = len1;
    __CPROVER_assume(to->len <= to->capacity);

    /* Need arbitrary cursor */
    struct aws_byte_cursor *from;
    ASSUME_VALID_MEMORY(from);
    from->ptr = malloc(len2);
    __CPROVER_assume(from->len <= len2);

    aws_byte_buf_append(to, from);
}
