/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_hash_callback_c_str_eq_harness() {
    const char *str1 = ensure_c_str_is_allocated(MAX_STRING_LEN);
    const char *str2 = nondet_bool() ? str1 : ensure_c_str_is_allocated(MAX_STRING_LEN);

    __CPROVER_assume(aws_c_string_is_valid(str1));
    __CPROVER_assume(aws_c_string_is_valid(str2));

    bool rval = aws_hash_callback_c_str_eq(str1, str2);
    if (rval) {
        size_t len = strlen(str1);
        assert_bytes_match(str1, str2, len);
    }
}
