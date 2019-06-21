/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

/**
 * FUNCTION: s_sift_either
 *
 * This function overrides the original implementation of the
 * s_sift_either function from priority_queue.h with a no_op.
 *
 * It is necessary to stub out s_sift_either because in order for it
 * to work, we have to have initialized all backpointers of the
 * priority queue correctly (which needs a loop).
 *
 * It is safe to stub out s_sift_either as long as we don't make any
 * assertions on the positions of elements in the priority queue and
 * their relative values.
 *
 */

#include <aws/common/priority_queue.h>

bool __CPROVER_file_local_priority_queue_c_s_sift_either(struct aws_priority_queue *queue, size_t index) {
    assert(aws_priority_queue_is_valid(queue));
    assert(index < queue->container.length);
    bool did_move;
    return did_move;
}
