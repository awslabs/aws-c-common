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

#include <aws/common/array_list.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 10s
 */
void aws_array_list_copy_harness() {
    /* data structure */
    struct aws_array_list from;
    struct aws_array_list to;

    /* assumptions */
    __CPROVER_assume(aws_array_list_is_bounded(&from, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&from);
    __CPROVER_assume(aws_array_list_is_valid(&from));

    __CPROVER_assume(aws_array_list_is_bounded(&to, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_array_list_has_allocated_data_member(&to);
    __CPROVER_assume(aws_array_list_is_valid(&to));

    /* perform operation under verification */
    if (aws_array_list_copy(&from, &to) == AWS_OP_SUCCESS) {
        /* In the case aws_array_list_copy is successful, both lists have the same length */
        assert(to.length == from.length);
	assert(from.item_size == to.item_size);
        assert(to.current_size >= (from.length * from.item_size));
    }

    /* assertions */
    assert(aws_array_list_is_valid(&from));
    assert(aws_array_list_is_valid(&to));
}
