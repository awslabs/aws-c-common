/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_hash_callback_string_destroy_harness() {
    struct aws_string *str = nondet_allocate_string_bounded_length(MAX_STRING_LEN);

    __CPROVER_assume(aws_string_is_valid(str));

    aws_hash_callback_string_destroy(str);
}
