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

void aws_linked_list_push_front_harness() {
    /* data structure */
    struct aws_linked_list list;
    struct aws_linked_list_node to_add;

    ensure_linked_list_is_allocated(&list, MAX_LINKED_LIST_ITEM_ALLOCATION);

    struct aws_linked_list_node *old_first = list.head.next;
    /* perform operation under verification */
    aws_linked_list_push_front(&list, &to_add);

    /* assertions */
    assert(aws_linked_list_is_valid(&list));
    assert(aws_linked_list_node_prev_is_valid(&to_add));
    assert(aws_linked_list_node_next_is_valid(&to_add));
    assert(list.head.next == &to_add);
    assert(to_add.next == old_first);
}
