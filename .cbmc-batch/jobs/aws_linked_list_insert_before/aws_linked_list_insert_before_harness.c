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

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_insert_before_harness() {
    /* data structure */
    struct aws_linked_list_node before;
    struct aws_linked_list_node before_prev;
    struct aws_linked_list_node to_add;

    before.prev = &before_prev;
    before_prev.next = &before;

    /* perform operation under verification */
    aws_linked_list_insert_before(&before, &to_add);

    /* assertions */
    assert(aws_linked_list_node_prev_is_valid(&before));
    assert(aws_linked_list_node_prev_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&before_prev));

    assert(before.prev == &to_add);
    assert(before_prev.next == &to_add);
}
