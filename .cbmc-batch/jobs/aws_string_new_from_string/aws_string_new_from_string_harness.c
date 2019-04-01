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

//MAX_STRING_LEN is defined in the makefile

/**
 * Coverage: 0.94 (76 lines out of 81 statically-reachable lines in 17 functions reached)
 * Missing lines are error handeling for impossible conditions
 * Runtime: real	0m24.870s
 */
void aws_string_new_from_string_harness() {
    struct aws_string *str_a = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
    struct aws_string *str_b = aws_string_new_from_string(str_a->allocator, str_a);
    if (str_b) {
        assert(str_a->len == str_b->len);
        assert(str_b->bytes[str_b->len] == '\0');
        assert_bytes_match(str_a->bytes, str_b->bytes, str_a->len);
    }
}
