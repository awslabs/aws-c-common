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

#include "proof_helpers/make_common_data_structures.h"
#include "proof_helpers/proof_allocators.h"
#include <aws/common/string.h>
#include <stddef.h>

const size_t MAX_STRING_LEN = 16;
/**
 * Coverage: 1.00 (19 lines out of 19 statically-reachable lines in 6 functions reached)
 * Runtime: real	0m2.030s
 */
void aws_string_bytes_harness() {
    struct aws_string *str = make_arbitrary_aws_string_nondet_len(can_fail_allocator());
    assert(aws_string_bytes(str) == str->bytes);
}
