/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
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
