/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_string_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_SIZE);
    __CPROVER_assume(aws_string_is_valid(str));
    /*
     * #TODO: Currently, CBMC is unable to check all possible paths in these proof.
     * aws_hash_string function calls hashlittle2 function, which calculates two 32-bit
     * hash values. Internally, it contains two conditions that test for alignment to
     * 4 byte/2 byte boundaries, but CBMC is unable to correctly evaluate such conditions,
     * due to its pointer encoding. A potential fix to this problem is under development.
     * For more details, see https://github.com/diffblue/cbmc/pull/1086.
     */
    uint64_t rval = aws_hash_string(str);
}
