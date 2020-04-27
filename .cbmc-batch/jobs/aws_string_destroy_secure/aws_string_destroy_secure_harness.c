/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

void aws_string_destroy_secure_harness() {
    struct aws_string *str = ensure_string_is_allocated_bounded_length(MAX_STRING_LEN);
    char const *bytes = str->bytes;
    size_t len = str->len;
    bool nondet_parameter;
    aws_string_destroy_secure(nondet_parameter ? str : NULL);

    // Check that all bytes are 0.  Since the memory is freed, this will trigger a use-after-free check
    // Disabiling the check only for this bit of the harness.
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
    if (nondet_parameter) {
        if (len > 0) {
            size_t i;
            __CPROVER_assume(i < len);
            assert(bytes[i] == 0);
        }
    }
#pragma CPROVER check pop
}
