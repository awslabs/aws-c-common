/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
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
