/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

const size_t MAX_STRING_LEN = 16;

/**
 * 0.93 (70 lines out of 75 statically-reachable lines in 15 functions reached)
 * Missing lines are error handeling for impossible conditions
 * Runtime: real	0m23.729s
 */
void aws_string_new_from_c_str_harness() {
    size_t alloc_len;
    __CPROVER_assume(alloc_len <= MAX_STRING_LEN);
    size_t max_strlen;
    __CPROVER_assume(max_strlen < alloc_len);

    uint8_t *c_str = malloc(alloc_len);
    c_str[max_strlen] = '\0'; // Ensure that the string is no longer than max_strlen.
    // Note that strlen may be shorter than max_strlen if the string has another null character in it
    struct aws_string *aws_str = aws_string_new_from_c_str(can_fail_allocator(), c_str);
    if (aws_str) {
        assert(aws_str->bytes[aws_str->len] == 0);
        assert_bytes_match(aws_str->bytes, c_str, aws_str->len);
    }
}
