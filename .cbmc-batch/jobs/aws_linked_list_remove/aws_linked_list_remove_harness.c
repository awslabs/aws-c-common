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

void aws_linked_list_remove_harness() {
    /* data structure */
    struct aws_linked_list_node prev;
    struct aws_linked_list_node next;
    struct aws_linked_list_node node;

    /* Assume the preconditions */
    prev.next = &node;
    node.prev = &prev;
    next.prev = &node;
    node.next = &next;

    /* Note: The function has a precondition that node != NULL */

    /* perform operation under verification */
    aws_linked_list_remove(&node);

    /* assertions */
    assert(aws_linked_list_node_next_is_valid(&prev));
    assert(aws_linked_list_node_prev_is_valid(&next));

    assert(prev.next == &next);
    assert(node.next == NULL);
    assert(node.prev == NULL);
}
