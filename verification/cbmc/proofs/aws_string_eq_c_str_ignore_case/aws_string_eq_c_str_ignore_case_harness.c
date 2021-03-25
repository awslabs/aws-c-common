/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_string_eq_c_str_ignore_case_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    const char *c_str = ensure_c_str_is_allocated(MAX_STRING_LEN);
    if (aws_string_eq_c_str_ignore_case(str, c_str) && str && c_str) {
        assert(aws_string_is_valid(str));
        assert(aws_c_string_is_valid(c_str));
        assert(str->len == strlen(c_str));
    }
}
