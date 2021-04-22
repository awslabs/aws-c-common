/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/string.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stddef.h>

void aws_ptr_eq_harness() {
    void *p1;
    void *p2;
    bool rval = aws_ptr_eq(p1, p2);
    assert(rval == (p1 == p2));
}
