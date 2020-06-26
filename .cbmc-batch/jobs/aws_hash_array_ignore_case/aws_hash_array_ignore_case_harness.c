/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_hash_array_ignore_case_harness() {
    /* parameters */
    size_t length;
    __CPROVER_assume(length < MAX_BUFFER_SIZE);
    uint8_t *array = can_fail_malloc(length);
    __CPROVER_assume(AWS_MEM_IS_READABLE(array, length));

    /* operation under verification */
    uint64_t rval = aws_hash_array_ignore_case(array, length);

    /* assertions */
    assert(AWS_MEM_IS_READABLE(array, length));
}
