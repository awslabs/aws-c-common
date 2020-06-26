/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_init_harness() {
    /* data structure */
    struct aws_linked_list list;

    /* Note: list is assumed to be a valid pointer in the function's
     *       precondition */

    /* perform operation under verification */
    aws_linked_list_init(&list);

    /* assertions */
    assert(aws_linked_list_is_valid(&list));
}
