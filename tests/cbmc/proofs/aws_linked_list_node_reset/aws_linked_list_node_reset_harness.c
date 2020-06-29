/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_node_reset_harness() {
    /* data structure */
    struct aws_linked_list_node node; // Preconditions require node to not be NULL

    /* perform operation under verification */
    aws_linked_list_node_reset(&node);

    /* assertions */
    assert(AWS_IS_ZEROED(node));
}
