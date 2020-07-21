/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/priority_queue.h>
#include <proof_helpers/make_common_data_structures.h>

/**
 * Runtime: 8s
 */
void aws_priority_queue_clean_up_harness() {
    /* data structure */
    struct aws_priority_queue queue;

    /* assumptions */
    __CPROVER_assume(aws_priority_queue_is_bounded(&queue, MAX_INITIAL_ITEM_ALLOCATION, MAX_ITEM_SIZE));
    ensure_priority_queue_has_allocated_members(&queue);
    __CPROVER_assume(aws_priority_queue_is_valid(&queue));

    /* perform operation under verification */
    aws_priority_queue_clean_up(&queue);

    /* assertions */
    assert(AWS_IS_ZEROED(queue.container));
    assert(AWS_IS_ZEROED(queue.backpointers));
}
