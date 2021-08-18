/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>

void aws_string_compare_harness() {
    struct aws_string *str_a = nondet_bool() ? nondet_allocate_string_bounded_length(MAX_STRING_LEN) : NULL;
    struct aws_string *str_b =
        nondet_bool() ? (nondet_bool() ? str_a : NULL) : nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    __CPROVER_assume(IMPLIES(str_a != NULL, aws_string_is_valid(str_a)));
    __CPROVER_assume(IMPLIES(str_b != NULL, aws_string_is_valid(str_b)));
    bool nondet_parameter = nondet_bool();
    if (aws_string_compare(str_a, nondet_parameter ? str_b : str_a) == AWS_OP_SUCCESS) {
        if (nondet_parameter && str_a && str_b) {
            assert_bytes_match(str_a->bytes, str_b->bytes, str_a->len);
        }
    }
    if (str_a) {
        assert(aws_string_is_valid(str_a));
    }
    if (str_b) {
        assert(aws_string_is_valid(str_b));
    }
}
