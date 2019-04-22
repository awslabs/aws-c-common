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

void aws_byte_buf_from_c_str_harness() {
    size_t len = nondet_size_t();

    char *c_str;
    ASSUME_VALID_MEMORY_COUNT(c_str, len);

    /* Need *c_str to be a '\0'-terminated C string, so assume an arbitrary character is 0 */
    int index = nondet_int();
    __CPROVER_assume(index >= 0 && index < len);
    c_str[index] = 0;

    /* Assume the length of the string is bounded by some max length */
    __CPROVER_assume(len <= MAX_STR_LEN);

    aws_byte_buf_from_c_str(c_str);
}
