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

#define aws_linked_list_of(type, name) struct name {                                                                   \
    type value;                                                                                                        \
    struct aws_linked_list_node list;                                                                                  \
}                                                                                                                      \

#define aws_container_of(ptr, type, member)  \
    ((type *)((uint8_t *)(ptr) - offsetof(type, member)))

#define aws_linked_list_push_back(head, new_node) \
    aws_linked_list_insert_before((head), (new_node))

#define aws_linked_list_push_front(head, new_node) \
    aws_linked_list_insert_after((head), (new_node))

#define aws_linked_list_pop_back(head) \
    aws_linked_list_remove((head)->prev)

#define aws_linked_list_pop_front(head) \
    head = aws_linked_list_remove(head);

#define aws_linked_list_insert_before(head, new_node) \
    aws_linked_list_insert_after(head->prev, new_node) 

struct aws_linked_list_node {
    struct aws_linked_list_node *next;
    struct aws_linked_list_node *prev;
};

#ifdef __cplusplus
extern "C" {
#endif

    /**
     * Initializes a circular doubly-linked list.
     */
    static inline AWS_COMMON_API void aws_linked_list_init(struct aws_linked_list_node *head);

    /**
     * Adds a node after the specified head.
     */
    static inline AWS_COMMON_API void aws_linked_list_insert_after(struct aws_linked_list_node *head, struct aws_linked_list_node *new_node);

    /**
     * Tests if the list is empty.
     */
    static inline AWS_COMMON_API int aws_linked_list_empty(struct aws_linked_list_node *head);

    /**
     * Removes the specified node from the list (prev/next point to each other) and returns the next node in the list.
     * If the list is empty, this function returns NULL.
     */
    static inline AWS_COMMON_API struct aws_linked_list_node* aws_linked_list_remove(struct aws_linked_list_node *head);

#ifdef __cplusplus
}
#endif

static inline void aws_linked_list_init(struct aws_linked_list_node *head) {
    head->next = head;
    head->prev = head;
}

static inline void aws_linked_list_add(struct aws_linked_list_node *new_node,
        struct aws_linked_list_node *prev,
        struct aws_linked_list_node *next) {

    next->prev = new_node;
    new_node->next = next;
    new_node->prev = prev;
    prev->next = new_node;
}

void aws_linked_list_insert_after(struct aws_linked_list_node *head, struct aws_linked_list_node *new_node) {
    aws_linked_list_add(new_node, head, head->next);
}

struct aws_linked_list_node *aws_linked_list_remove(struct aws_linked_list_node *head) {
    head->prev->next = head->next;
    head->next->prev = head->prev;
    struct aws_linked_list_node *next = head->next;
    head->next = head;
    head->prev = head;
    return next;
}

int aws_linked_list_empty(struct aws_linked_list_node *head) {
    return head->next == head;
}

#endif /*AWS_LINKED_LIST_H */

