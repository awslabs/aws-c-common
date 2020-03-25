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

void aws_linked_list_prev_harness() {
    /* data structure */
    struct aws_linked_list_node node;   // Preconditions require node to not be NULL
    struct aws_linked_list_node before; // Preconditions require before to not be NULL

    /* Assume the preconditions */
    node.prev = &before;
    before.next = &node;

    /* perform operation under verification */
    struct aws_linked_list_node *rval = aws_linked_list_prev(&node);

    /* assertions */
    assert(aws_linked_list_node_prev_is_valid(&node));
    assert(aws_linked_list_node_next_is_valid(rval));
    assert(rval == &before);
}
