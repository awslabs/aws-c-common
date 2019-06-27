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

void aws_string_eq_c_str_ignore_case_harness() {
    struct aws_string *str = make_arbitrary_aws_string_nondet_len_with_max(MAX_STRING_LEN);
    const char *c_str = nondet_bool() ? make_arbitrary_c_str(MAX_STRING_LEN) : NULL;
    if (aws_string_eq_c_str_ignore_case(str, c_str)) {
        assert(str->len == strlen(c_str));
    }
    assert(aws_string_is_valid(str));
}
