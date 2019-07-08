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

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_string_harness() {
    struct aws_string *str = ensure_string_is_allocated_bounded_length(MAX_STRING_SIZE);
    /*
     * aws_hash_string has no pre or post conditions. #TODO: Currently, CBMC is unable to
     * check all possible paths in these proof. aws_hash_string function calls hashlittle2
     * function, which calculates two 32-bit hash values. Internally, it contains two
     * conditions that test for alignment to 4 byte/2 byte boundaries, but CBMC is unable
     * to correctly evaluate such conditions, due to its pointer encoding. A potential
     * fix to this problem is under development.
     * For more details, see https://github.com/diffblue/cbmc/pull/1086.
     */
    uint64_t rval = aws_hash_string(str);
}
