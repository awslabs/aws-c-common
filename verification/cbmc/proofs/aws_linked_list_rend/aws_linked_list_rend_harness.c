/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/linked_list.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_linked_list_rend_harness() {
    /* data structure */
    struct aws_linked_list list;

    ensure_linked_list_is_allocated(&list, MAX_LINKED_LIST_ITEM_ALLOCATION);

    /* Assume the preconditions */
    __CPROVER_assume(aws_linked_list_is_valid(&list));

    /* Note: list can never be a NULL pointer as is_valid checks for that */

    /* perform operation under verification */
    struct aws_linked_list_node const *rval = aws_linked_list_rend(&list);

    /* assertions */
    assert(rval == &list.head);
    assert(aws_linked_list_is_valid(&list));
}
