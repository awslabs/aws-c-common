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

// MAX_STRING_LEN is defined in the makefile

/**
 * Coverage: 0.93 (68 lines out of 73 statically-reachable lines in 14 functions reached)
 * Missing lines are error handeling for impossible conditions
 * Runtime: real	0m23.611s
 */
void aws_string_new_from_array_harness() {
    size_t alloc_len;
    __CPROVER_assume(alloc_len <= MAX_STRING_LEN);
    uint8_t *array = malloc(alloc_len);
    size_t reported_size;
    __CPROVER_assume(reported_size <= alloc_len);
    struct aws_string *aws_str = aws_string_new_from_array(can_fail_allocator(), array, reported_size);
    if (aws_str) {
        assert(aws_str->len == reported_size);
        assert(aws_str->bytes[aws_str->len] == 0);
        assert_bytes_match(aws_str->bytes, array, aws_str->len);
    }
}
