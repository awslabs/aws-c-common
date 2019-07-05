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

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_array_list_comparator_string_harness() {
    struct aws_string *str_a = ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    struct aws_string *str_b = nondet_bool() ? str_a : ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    bool nondet_parameter_a;
    bool nondet_parameter_b;
    if (aws_array_list_comparator_string(nondet_parameter_a ? &str_a : NULL, nondet_parameter_b ? &str_b : NULL) == 0) {
        if (nondet_parameter_a && nondet_parameter_b) {
            assert_bytes_match(str_a->bytes, str_b->bytes, str_a->len);
        }
    }
}
