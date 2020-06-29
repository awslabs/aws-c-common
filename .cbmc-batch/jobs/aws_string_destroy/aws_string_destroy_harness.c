/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/proof_allocators.h>

void aws_string_destroy_harness() {
    struct aws_string *str = nondet_bool() ? ensure_string_is_allocated_nondet_length() : NULL;
    aws_string_destroy(str);
}
