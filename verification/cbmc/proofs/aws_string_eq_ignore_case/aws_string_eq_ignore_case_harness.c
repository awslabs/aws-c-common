/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>

void aws_string_eq_ignore_case_harness() {
    struct aws_string *str_a = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    struct aws_string *str_b = nondet_bool() ? str_a : nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    __CPROVER_assume(IMPLIES(str_a != NULL, aws_string_is_valid(str_a)));
    __CPROVER_assume(IMPLIES(str_b != NULL && str_a != str_b, aws_string_is_valid(str_b)));
    if (aws_string_eq_ignore_case(str_a, str_b) && str_a && str_b) {
        assert(aws_string_is_valid(str_a));
        assert(aws_string_is_valid(str_b));
        assert(str_a->len == str_b->len);
    }
}
