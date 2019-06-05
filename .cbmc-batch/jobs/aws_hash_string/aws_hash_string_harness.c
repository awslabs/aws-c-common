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
    struct aws_string *str =
        make_arbitrary_aws_string_nondet_len_with_max(nondet_bool() ? NULL : can_fail_allocator(), MAX_STRING_SIZE);
    /* This function has no pre or post conditions. Currently, CBMC is unable to check
     * all possible paths in these proof, but https://github.com/diffblue/cbmc/pull/1086
     * should fix this. */
    uint64_t rval = aws_hash_string(str);
}
