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

#include <assert.h>
#include <string.h>

#define PARENT_OF(index) (((index)&1) ? (index) >> 1 : (index) > 1 ? ((index)-2) >> 1 : 0)
#define LEFT_OF(index) (((index) << 1) + 1)
#define RIGHT_OF(index) (((index) << 1) + 2)

static void s_swap(struct aws_priority_queue *queue, size_t a, size_t b) {
    aws_array_list_swap(&queue->container, a, b);

    /* Invariant: If the backpointer array is initialized, we have enough room for all elements */
    if (queue->backpointers.data) {
        assert(queue->backpointers.length > a);
        assert(queue->backpointers.length > b);

        struct aws_priority_queue_node **bp_a = &((struct aws_priority_queue_node **)queue->backpointers.data)[a];
        struct aws_priority_queue_node **bp_b = &((struct aws_priority_queue_node **)queue->backpointers.data)[b];

        struct aws_priority_queue_node *tmp = *bp_a;
        *bp_a = *bp_b;
        *bp_b = tmp;

        if (*bp_a) {
            (*bp_a)->current_index = a;
        }

        if (*bp_b) {
            (*bp_b)->current_index = b;
        }
    }
}

/* Precondition: with the exception of the given root element, the container must be
 * in heap order */
static bool s_sift_down(struct aws_priority_queue *queue, size_t root) {
    bool did_move = false;

    size_t len = aws_array_list_length(&queue->container);

    while (LEFT_OF(root) < len) {
        size_t left = LEFT_OF(root);
        size_t right = RIGHT_OF(root);
        size_t first = root;
        void *first_item = NULL, *other_item = NULL;

        aws_array_list_get_at_ptr(&queue->container, &first_item, root);
        aws_array_list_get_at_ptr(&queue->container, &other_item, left);

        if (queue->pred(first_item, other_item) > 0) {
            first = left;
            first_item = other_item;
        }

        if (right < len) {
            aws_array_list_get_at_ptr(&queue->container, &other_item, right);

            /* choose the larger/smaller of the two in case of a max/min heap
             * respectively */
            if (queue->pred(first_item, other_item) > 0) {
                first = right;
                first_item = other_item;
            }
        }

        if (first != root) {
            s_swap(queue, first, root);
            did_move = true;
            root = first;
        } else {
            break;
        }
    }

    return did_move;
}

/* Precondition: Elements prior to the specified index must be in heap order. */
static bool s_sift_up(struct aws_priority_queue *queue, size_t index) {
    bool did_move = false;

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
            s_swap(queue, index, parent);
            did_move = true;
            index = parent;
            parent = PARENT_OF(index);
        } else {
            break;
        }
    }

    return did_move;
}

/*
 * Precondition: With the exception of the given index, the heap condition holds for all elements.
 * In particular, the parent of the current index is a predecessor of all children of the current index.
 */
static void s_sift_either(struct aws_priority_queue *queue, size_t index) {
    if (!index || !s_sift_up(queue, index)) {
        s_sift_down(queue, index);
    }
}

int aws_priority_queue_init_dynamic(
    struct aws_priority_queue *queue,
    struct aws_allocator *alloc,
    size_t default_size,
    size_t item_size,
    aws_priority_queue_compare_fn *pred) {

    queue->pred = pred;
    memset(&queue->backpointers, 0, sizeof(queue->backpointers));

    return aws_array_list_init_dynamic(&queue->container, alloc, default_size, item_size);
}

void aws_priority_queue_init_static(
    struct aws_priority_queue *queue,
    void *heap,
    size_t item_count,
    size_t item_size,
    aws_priority_queue_compare_fn *pred) {

    queue->pred = pred;
    memset(&queue->backpointers, 0, sizeof(queue->backpointers));

    aws_array_list_init_static(&queue->container, heap, item_count, item_size);
}

void aws_priority_queue_clean_up(struct aws_priority_queue *queue) {
    aws_array_list_clean_up(&queue->container);
    aws_array_list_clean_up(&queue->backpointers);
}

int aws_priority_queue_push(struct aws_priority_queue *queue, void *item) {
    return aws_priority_queue_push_ref(queue, item, NULL);
}

int aws_priority_queue_push_ref(
    struct aws_priority_queue *queue,
    void *item,
    struct aws_priority_queue_node *backpointer) {
    int err = aws_array_list_push_back(&queue->container, item);
    if (err) {
        return err;
    }

    size_t index = aws_array_list_length(&queue->container) - 1;

    if (backpointer && !queue->backpointers.alloc) {
        if (!queue->container.alloc) {
            aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
            goto backpointer_update_failed;
        }

        if (aws_array_list_init_dynamic(
                &queue->backpointers, queue->container.alloc, index + 1, sizeof(struct aws_priority_queue_node *))) {
            goto backpointer_update_failed;
        }

        /* When we initialize the backpointers array we need to zero out all existing entries */
        memset(queue->backpointers.data, 0, queue->backpointers.current_size);
    }

    /*
     * Once we have any backpointers, we want to make sure we always have room in the backpointers array
     * for all elements; otherwise, sift_down gets complicated if it runs out of memory when sifting an
     * element with a backpointer down in the array.
     */
    if (queue->backpointers.data) {
        if (aws_array_list_set_at(&queue->backpointers, &backpointer, index)) {
            goto backpointer_update_failed;
        }
    }

    if (backpointer) {
        backpointer->current_index = index;
    }

    s_sift_up(queue, aws_array_list_length(&queue->container) - 1);

    return AWS_OP_SUCCESS;

backpointer_update_failed:
    /* Failed to initialize or grow the backpointer array, back out the node addition */
    aws_array_list_pop_back(&queue->container);
    return AWS_OP_ERR;
}

static int s_remove_node(struct aws_priority_queue *queue, void *item, size_t item_index) {
    if (aws_array_list_get_at(&queue->container, item, item_index)) {
        /* shouldn't happen, but if it does we've already raised an error... */
        return AWS_OP_ERR;
    }

    size_t swap_with = aws_array_list_length(&queue->container) - 1;
    struct aws_priority_queue_node *backpointer = NULL;

    if (item_index != swap_with) {
        s_swap(queue, item_index, swap_with);
    }

    aws_array_list_get_at(&queue->backpointers, &backpointer, swap_with);
    if (backpointer) {
        backpointer->current_index = SIZE_MAX;
    }

    aws_array_list_pop_back(&queue->container);
    aws_array_list_pop_back(&queue->backpointers);

    if (item_index != swap_with) {
        s_sift_either(queue, item_index);
    }

    return AWS_OP_SUCCESS;
}

int aws_priority_queue_remove(
    struct aws_priority_queue *queue,
    void *item,
    const struct aws_priority_queue_node *node) {
    if (node->current_index >= aws_array_list_length(&queue->container) || !queue->backpointers.data) {
        return aws_raise_error(AWS_ERROR_PRIORITY_QUEUE_BAD_NODE);
    }

    return s_remove_node(queue, item, node->current_index);
}

int aws_priority_queue_pop(struct aws_priority_queue *queue, void *item) {
    if (0 == aws_array_list_length(&queue->container)) {
        return aws_raise_error(AWS_ERROR_PRIORITY_QUEUE_EMPTY);
    }

    return s_remove_node(queue, item, 0);
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
