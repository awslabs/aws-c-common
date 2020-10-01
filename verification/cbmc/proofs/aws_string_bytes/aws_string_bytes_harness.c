/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_string_bytes_harness() {
    struct aws_string *str = ensure_string_is_allocated_nondet_length();
    __CPROVER_assume(aws_string_is_valid(str));
    assert(aws_string_bytes(str) == str->bytes);
    assert(aws_string_is_valid(str));
}
