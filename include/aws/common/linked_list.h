#ifndef AWS_LINKED_LIST_H
#define AWS_LINKED_LIST_H

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
#include <assert.h>

/**
 * from a pointer and a type of the struct containing the node
 * this will get you back to the pointer of the object. member is the name of
 * the instance of struct aws_linked_list_node in your struct.
 */
#define aws_container_of(ptr, type, member)  \
    ((type *)((uint8_t *)(ptr) - offsetof(type, member)))

struct aws_linked_list_node {
    struct aws_linked_list_node *next;
    struct aws_linked_list_node *prev;
};

struct aws_linked_list {
    struct aws_linked_list_node head;
    struct aws_linked_list_node tail;
};

/**
 * Initializes the list. List will be empty after this call.
 */
static inline void aws_linked_list_init(struct aws_linked_list *list) {
    list->head.next = &list->tail;
    list->head.prev = NULL;
    list->tail.prev = &list->head;
    list->tail.next = NULL;
}

/**
 * Tests if the list is empty.
 */
static inline int aws_linked_list_empty(struct aws_linked_list *list) {
    return list->head.next == &list->tail;
}

/**
 * Removes the specified node from the list (prev/next point to each other) and returns the next node in the list.
 * If the list is empty, this function returns NULL.
 */
static inline void aws_linked_list_remove(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    assert(!aws_linked_list_empty(list));
    node->prev->next = node->next;
    node->next->prev = node->prev;
}

/**
 * Append new_node.
 */
static inline void aws_linked_list_push_back(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    list->tail.prev->next = node;
    node->next = &list->tail;
    node->prev = list->tail.prev;
    list->tail.prev = node;
}

/**
 * Returns the element in the back of the list.
 */
static struct aws_linked_list_node *aws_linked_list_back(struct aws_linked_list *list) {
    assert(!aws_linked_list_empty(list));
    return list->tail.prev;
}

/**
 * Returns the element in the back of the list and removes it
 */
static inline struct aws_linked_list_node *aws_linked_list_pop_back(struct aws_linked_list *list) {
    assert(!aws_linked_list_empty(list));
    struct aws_linked_list_node *back = aws_linked_list_back(list);
    aws_linked_list_remove(list, back);
    return back;
}

/**
 * Prepend new_node.
 */
static inline void aws_linked_list_push_front(struct aws_linked_list *list, struct aws_linked_list_node *node) {
    list->head.next->prev = node;
    node->next = list->head.next;
    node->prev = &list->head;
    list->head.next = node;
}

/**
 * Returns the element in the front of the list.
 */
static inline struct aws_linked_list_node * aws_linked_list_front(struct aws_linked_list *list) {
    assert(!aws_linked_list_empty(list));
    return list->head.next;
}

/**
 * Returns the element in the front of the list and removes it
 */
static inline struct aws_linked_list_node *aws_linked_list_pop_front(struct aws_linked_list *list) {
    assert(!aws_linked_list_empty(list));
    struct aws_linked_list_node *front = aws_linked_list_front(list);
    aws_linked_list_remove(list, front);
    return front;
}

#endif /*AWS_LINKED_LIST_H */
