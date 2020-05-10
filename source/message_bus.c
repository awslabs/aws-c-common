/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/allocator.h>
#include <aws/common/byte_buf.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/message_bus.h>
#include <aws/common/mutex.h>
#include <aws/common/ring_buffer.h>

struct aws_message_bus {
    struct aws_allocator *allocator;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
        struct aws_mutex mutex;
    } slots;

    /* Storage for messages until they are delivered */
    struct aws_ring_buffer buffer;
};

struct bus_listener {
    struct aws_linked_list_node list_node;
    void *user_data;
    aws_message_bus_listener_fn *deliver;
};

struct listener_list {
    struct aws_message_bus *bus;
    struct aws_linked_list listeners;
};

void s_destroy_listener_list(void *data) {
    struct listener_list *list = data;
    AWS_PRECONDITION(list->bus);
    /* call all listeners with a 0 message type to clean up */
    while (!aws_linked_list_empty(&list->listeners)) {
        struct aws_linked_list_node *back = aws_linked_list_back(&list->listeners);
        struct bus_listener *listener = AWS_CONTAINER_OF(back, struct bus_listener, list_node);
        listener->deliver(0, NULL, NULL);
        aws_linked_list_pop_back(&list->listeners);
        aws_mem_release(list->bus->allocator, listener);
    }
    aws_mem_release(list->bus->allocator, list);
}

struct aws_message_bus *aws_message_bus_new(struct aws_allocator *allocator, size_t buffer_size) {
    struct aws_message_bus *bus =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_message_bus));

    bus->allocator = allocator;
    if (aws_mutex_init(&bus->slots.mutex)) {
        goto error;
    }
    if (aws_hash_table_init(&bus->slots.table, allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_listener_list)) {
        goto error;
    }

    if (aws_ring_buffer_init(&bus->buffer, allocator, buffer_size)) {
        goto error;
    }

    return bus;

error:
    aws_ring_buffer_clean_up(&bus->buffer);
    aws_hash_table_clean_up(&bus->slots.table);
    aws_mutex_clean_up(&bus->slots.mutex);
    aws_mem_release(allocator, bus);
    return NULL;
}

void aws_message_bus_destroy(struct aws_message_bus *bus) {
    /* clean up listeners */
    aws_hash_table_clean_up(&bus->slots.table);
    aws_mutex_clean_up(&bus->slots.mutex);
    aws_ring_buffer_clean_up(&bus->buffer);
    aws_mem_release(bus->allocator, bus);
}

int aws_message_bus_new_message(struct aws_message_bus *bus, size_t size, struct aws_byte_buf **msg) {
    AWS_PRECONDITION(msg);
    return aws_ring_buffer_acquire(&bus->buffer, size, *msg);
}

void aws_message_bus_destroy_message(struct aws_message_bus *bus, struct aws_byte_buf *msg) {
    AWS_PRECONDITION(msg);
    aws_ring_buffer_release(&bus->buffer, msg);
}

int aws_message_bus_subscribe(struct aws_message_bus *bus, uintptr_t msg_type, aws_message_bus_listener_fn *listener, void *user_data) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_unsubscribe(struct aws_message_bus *bus, uintptr_t msg_type, aws_message_bus_listener_fn *listener, void *user_data) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_send(struct aws_message_bus *bus, uintptr_t msg_type, struct aws_byte_buf *msg) {
    return AWS_OP_SUCCESS;
}
