#ifndef AWS_COMMON_LINKED_LIST_H
#define AWS_COMMON_LINKED_LIST_H

/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/common.h>

#include <stddef.h>

struct aws_linked_list_node {
    struct aws_linked_list_node *next;
    struct aws_linked_list_node *prev;
};

/**
 * Set node's next and prev pointers to NULL.
 */
AWS_STATIC_IMPL void aws_linked_list_node_reset(struct aws_linked_list_node *node) {
    AWS_ZERO_STRUCT(*node);
}

struct aws_linked_list {
    struct aws_linked_list_node head;
    struct aws_linked_list_node tail;
};

/**
 * These functions need to be defined first as they are used in pre
 * and post conditions.
 */

/**
 * Tests if the list is empty.
 */
AWS_STATIC_IMPL bool aws_linked_list_empty(const struct aws_linked_list *list) {
    return list->head.next == &list->tail;
}

/**
 * Checks that a linked list is valid.
 */
AWS_STATIC_IMPL bool aws_linked_list_is_valid(const struct aws_linked_list *list) {
    if (list && list->head.next && list->head.prev == NULL && list->tail.prev && list->tail.next == NULL) {
#if (AWS_DEEP_CHECKS == 1)
        return aws_linked_list_is_valid_deep(list);
#else
        return true;
#endif
    }
    return false;
}

/**
 * Checks that the prev of the next pointer of a node points to the
 * node. As this checks whether the [next] connection of a node is
 * bidirectional, it returns false if used for the list tail.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_next_is_valid(const struct aws_linked_list_node *node) {
    return node && node->next && node->next->prev == node;
}

/**
 * Checks that the next of the prev pointer of a node points to the
 * node. Similarly to the above, this returns false if used for the
 * head of a list.
 */
AWS_STATIC_IMPL bool aws_linked_list_node_prev_is_valid(const struct aws_linked_list_node *node) {
    return node && node->prev && node->prev->next == node;
}

/**
 * Checks that a linked list satisfies double linked list connectivity
 * constraints. This check is O(n) as it traverses the whole linked
 * list to ensure that tail is reachable from head (and vice versa)
 * and that every connection is bidirectional.
 *
 * Note: This check could go into an inginite loop if the list is
 * circular.
 */
AWS_STATIC_IMPL bool aws_linked_list_is_valid_deep(const struct aws_linked_list *list) {
    if (!list) {
        return false;
    }
    /* This could go into an infinite loop for a circular list */
    const struct aws_linked_list_node *temp = &list->head;
    /* Head must reach tail by following next pointers */
    bool head_reaches_tail = false;
    /* Next and prev pointers should connect the same nodes */
    bool are_links_valid = true;
    /* By satisfying both of the above, we also guarantee that tail
     * reaches head by following prev pointers */
    while (temp) {
        if (temp == &list->tail) {
            head_reaches_tail = true;
            break;
        } else if (!aws_linked_list_node_next_is_valid(temp)) {
            are_links_valid = false;
            break;
        }
        temp = temp->next;
    }
    return head_reaches_tail && are_links_valid;
}

/**
 * Initializes the list. List will be empty after this call.
 */
AWS_STATIC_IMPL void aws_linked_list_init(struct aws_linked_list *list) {
    AWS_PRECONDITION(list);
    list->head.next = &list->tail;
    list->head.prev = NULL;
    list->tail.prev = &list->head;
    list->tail.next = NULL;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    AWS_POSTCONDITION(aws_linked_list_empty(list));
}

/**
 * Returns an iteration pointer for the first element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_begin(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *rval = list->head.next;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return rval;
}

/**
 * Returns an iteration pointer for one past the last element in the list.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_end(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    const struct aws_linked_list_node *rval = &list->tail;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return rval;
}

/**
 * Returns a pointer for the last element in the list.
 * Used to begin iterating the list in reverse. Ex:
 *   for (i = aws_linked_list_rbegin(list); i != aws_linked_list_rend(list); i = aws_linked_list_prev(i)) {...}
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_rbegin(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    struct aws_linked_list_node *rval = list->tail.prev;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return rval;
}

/**
 * Returns the pointer to one before the first element in the list.
 * Used to end iterating the list in reverse.
 */
AWS_STATIC_IMPL const struct aws_linked_list_node *aws_linked_list_rend(const struct aws_linked_list *list) {
    AWS_PRECONDITION(aws_linked_list_is_valid(list));
    const struct aws_linked_list_node *rval = &list->head;
    AWS_POSTCONDITION(aws_linked_list_is_valid(list));
    return rval;
}

/**
 * Returns the next element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_next(const struct aws_linked_list_node *node) {
    return node->next;
}

/**
 * Returns the previous element in the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_prev(const struct aws_linked_list_node *node) {
    return node->prev;
}

/**
 * Inserts to_add immediately after after.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_after(
    struct aws_linked_list_node *after,
    struct aws_linked_list_node *to_add) {
    to_add->prev = after;
    to_add->next = after->next;
    after->next->prev = to_add;
    after->next = to_add;
}

/**
 * Inserts to_add immediately before before.
 */
AWS_STATIC_IMPL void aws_linked_list_insert_before(
    struct aws_linked_list_node *before,
    struct aws_linked_list_node *to_add) {
    to_add->next = before;
    to_add->prev = before->prev;
    before->prev->next = to_add;
    before->prev = to_add;
}

/**
 * Removes the specified node from the list (prev/next point to each other) and
 * returns the next node in the list.
 */
AWS_STATIC_IMPL void aws_linked_list_remove(struct aws_linked_list_node *node) {
    node->prev->next = node->next;
    node->next->prev = node->prev;
    aws_linked_list_node_reset(node);
}

/**
 * Append new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_back(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    aws_linked_list_insert_before(&list->tail, node);
}

/**
 * Returns the element in the back of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_back(const struct aws_linked_list *list) {
    AWS_ASSERT(!aws_linked_list_empty(list));
    return list->tail.prev;
}

/**
 * Returns the element in the back of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_back(struct aws_linked_list *list) {
    AWS_ASSERT(!aws_linked_list_empty(list));
    struct aws_linked_list_node *back = aws_linked_list_back(list);
    aws_linked_list_remove(back);
    return back;
}

/**
 * Prepend new_node.
 */
AWS_STATIC_IMPL void aws_linked_list_push_front(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    aws_linked_list_insert_before(list->head.next, node);
}

/**
 * Returns the element in the front of the list.
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_front(const struct aws_linked_list *list) {
    AWS_ASSERT(!aws_linked_list_empty(list));
    return list->head.next;
}

/**
 * Returns the element in the front of the list and removes it
 */
AWS_STATIC_IMPL struct aws_linked_list_node *aws_linked_list_pop_front(struct aws_linked_list *list) {
    AWS_ASSERT(!aws_linked_list_empty(list));
    struct aws_linked_list_node *front = aws_linked_list_front(list);
    aws_linked_list_remove(front);
    return front;
}

AWS_STATIC_IMPL void aws_linked_list_swap_contents(struct aws_linked_list *a, struct aws_linked_list *b) {
    AWS_ASSERT(a);
    AWS_ASSERT(b);
    struct aws_linked_list_node *a_first = a->head.next;
    struct aws_linked_list_node *a_last = a->tail.prev;

    /* Move B's contents into A */
    if (aws_linked_list_empty(b)) {
        aws_linked_list_init(a);
    } else {
        a->head.next = b->head.next;
        a->head.next->prev = &a->head;
        a->tail.prev = b->tail.prev;
        a->tail.prev->next = &a->tail;
    }

    /* Move A's old contents into B */
    if (a_first == &a->tail) {
        aws_linked_list_init(b);
    } else {
        b->head.next = a_first;
        b->head.next->prev = &b->head;
        b->tail.prev = a_last;
        b->tail.prev->next = &b->tail;
    }
}

#endif /* AWS_COMMON_LINKED_LIST_H */
