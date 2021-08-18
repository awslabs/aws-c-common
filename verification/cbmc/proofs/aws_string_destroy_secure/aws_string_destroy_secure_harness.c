/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_string_destroy_secure_harness() {
    /* Non-deterministic parameters. */
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);
    char const *bytes;
    size_t len;
    bool is_str_null = (str == NULL);

    /* Assumptions. */
    __CPROVER_assume(IMPLIES(str != NULL, aws_string_is_valid(str)));
    struct aws_string old_str = {0};
    if (str != NULL) {
        old_str = *str;
    }

    /* Operation under verification. */
    aws_string_destroy_secure(str);

    /* Check that all bytes are 0.  Since the memory is freed,
     * this will trigger a use-after-free check
     * Disabiling the check only for this bit of the harness. */
#pragma CPROVER check push
#pragma CPROVER check disable "pointer"
    if (old_str.bytes == NULL) {
        if (old_str.len > 0) {
            size_t i;
            __CPROVER_assume(i < old_str.len);
            assert(old_str.bytes[i] == 0);
        }
    }
#pragma CPROVER check pop
}
