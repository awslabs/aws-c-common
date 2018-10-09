/*
 * Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/priority_queue.h>

#include <string.h>

#define PARENT_OF(index) (((index)&1) ? (index) >> 1 : (index) > 1 ? ((index)-2) >> 1 : 0)
#define LEFT_OF(index) (((index) << 1) + 1)

/* Precondition: with the exception of the first element, the container must be
 * in heap order */
static void s_sift_down(struct aws_priority_queue *queue) {
    size_t root = 0;
    size_t left = LEFT_OF(root);
    size_t len = aws_array_list_length(&queue->container);
    void *right_item = NULL, *left_item = NULL, *root_item = NULL;

    while (left < len) {
        aws_array_list_get_at_ptr(&queue->container, &left_item, left);

        size_t right = left + 1;
        if (right < len) {
            aws_array_list_get_at_ptr(&queue->container, &right_item, right);

            /* choose the larger/smaller of the two in case of a max/min heap
             * respectively */
            if (queue->pred(left_item, right_item) > 0) {
                left = right;
                left_item = right_item;
            }
        }

        aws_array_list_get_at_ptr(&queue->container, &root_item, root);
        if (queue->pred(root_item, left_item) > 0) {
            aws_array_list_swap(&queue->container, left, root);
            root = left;
            left = LEFT_OF(root);
        } else {
            break;
        }
    }
}

/* Precondition: Elements prior to the specified index must be in heap order. */
static void s_sift_up(struct aws_priority_queue *queue, size_t index) {
    void *parent_item, *child_item;
    size_t parent = PARENT_OF(index);
    while (index) {
        /*
         * These get_ats are guaranteed to be successful; if they are not, we have
         * serious state corruption, so just abort.
         */

        if (aws_array_list_get_at_ptr(&queue->container, &parent_item, parent) ||
            aws_array_list_get_at_ptr(&queue->container, &child_item, index)) {
            abort();
        }

        if (queue->pred(parent_item, child_item) > 0) {
            aws_array_list_swap(&queue->container, index, parent);
            index = parent;
            parent = PARENT_OF(index);
        } else {
            break;
        }
    }
}

int aws_priority_queue_init_dynamic(
    struct aws_priority_queue *queue,
    struct aws_allocator *alloc,
    size_t default_size,
    size_t item_size,
    aws_priority_queue_compare_fn *pred) {

    queue->pred = pred;
    return aws_array_list_init_dynamic(&queue->container, alloc, default_size, item_size);
}

void aws_priority_queue_init_static(
    struct aws_priority_queue *queue,
    void *heap,
    size_t item_count,
    size_t item_size,
    aws_priority_queue_compare_fn *pred) {

    queue->pred = pred;
    aws_array_list_init_static(&queue->container, heap, item_count, item_size);
}

void aws_priority_queue_clean_up(struct aws_priority_queue *queue) {
    aws_array_list_clean_up(&queue->container);
}

int aws_priority_queue_push(struct aws_priority_queue *queue, void *item) {
    int err = aws_array_list_push_back(&queue->container, item);
    if (err) {
        return err;
    }

    s_sift_up(queue, aws_array_list_length(&queue->container) - 1);

    return AWS_OP_SUCCESS;
}

int aws_priority_queue_pop(struct aws_priority_queue *queue, void *item) {
    if (0 == aws_array_list_length(&queue->container)) {
        return aws_raise_error(AWS_ERROR_PRIORITY_QUEUE_EMPTY);
    }

    /* in this case aws_raise_error(..) has already been called */
    if (aws_array_list_get_at(&queue->container, item, 0)) {
        return AWS_OP_ERR;
    }

    aws_array_list_swap(&queue->container, 0, aws_array_list_length(&queue->container) - 1);
    if (aws_array_list_pop_back(&queue->container)) {
        return AWS_OP_ERR;
    }

    s_sift_down(queue);
    return AWS_OP_SUCCESS;
}

int aws_priority_queue_top(const struct aws_priority_queue *queue, void **item) {
    if (0 == aws_array_list_length(&queue->container)) {
        return aws_raise_error(AWS_ERROR_PRIORITY_QUEUE_EMPTY);
    }
    return aws_array_list_get_at_ptr(&queue->container, item, 0);
}

size_t aws_priority_queue_size(const struct aws_priority_queue *queue) {
    return aws_array_list_length(&queue->container);
}

size_t aws_priority_queue_capacity(const struct aws_priority_queue *queue) {
    return aws_array_list_capacity(&queue->container);
}
