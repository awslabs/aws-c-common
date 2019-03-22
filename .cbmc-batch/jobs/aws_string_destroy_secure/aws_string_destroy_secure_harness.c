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
 * Coverage: 1.00 (59 lines out of 59 statically-reachable lines in 15 functions reached)
 * Runtime: real	0m5.907s
 */
void aws_string_destroy_secure_harness() {
    struct aws_string *str = make_arbitrary_aws_string_nondet_len_with_max(can_fail_allocator(), MAX_STRING_LEN);
    assert(str);
    char *bytes = str->bytes;
    size_t len = str->len;
    __CPROVER_allocated_memory(bytes, len); // tell CBMC to keep the buffer live after the free
    aws_string_destroy_secure(str);
    assert_all_zeroes(bytes, len);
}
