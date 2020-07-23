/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_hash_callback_string_eq_harness() {
    const struct aws_string *str1 = ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    const struct aws_string *str2 = nondet_bool() ? str1 : ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    bool rval = aws_hash_callback_string_eq(str1, str2);
    if (rval) {
        assert(str1->len == str2->len);
        assert_bytes_match(str1->bytes, str2->bytes, str1->len);
    }
}
