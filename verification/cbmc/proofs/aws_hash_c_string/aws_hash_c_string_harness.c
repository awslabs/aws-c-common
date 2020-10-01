/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/hash_table.h>
#include <aws/common/private/hash_table_impl.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_hash_c_string_harness() {
    const char *str = ensure_c_str_is_allocated(MAX_STRING_SIZE);

    __CPROVER_assume(aws_c_string_is_valid(str));

    uint64_t rval = aws_hash_c_string(str);
}
