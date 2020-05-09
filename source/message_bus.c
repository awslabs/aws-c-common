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
#include <aws/common/linked_list.h>
#include <aws/common/message_bus.h>

struct aws_message_bus {
    struct aws_allocator *allocator;
    /* List of listeners that receive every message */
    struct aws_linked_list global_listeners;
    /* Array of listeners, length is number of slots */
    struct aws_linked_list *slots;
    size_t num_slots;
};

struct aws_message_bus *aws_message_bus_new(struct aws_allocator *allocator, size_t slots) {
    struct aws_message_bus *bus =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_message_bus) + (sizeof(struct aws_linked_list) * slots));

    bus->allocator = allocator;
    aws_linked_list_init(&bus->global_listeners);
    bus->slots = (struct aws_linked_list *)(((uint8_t *)bus) + sizeof(struct aws_message_bus));
    bus->num_slots = slots;

    for (size_t slot_idx = 0; slot_idx < slots; ++slot_idx) {
        struct aws_linked_list *slot = &bus->slots[slot_idx];
        aws_linked_list_init(slot);
    }
    return bus;
}

void aws_message_bus_destroy(struct aws_message_bus *bus) {
    /* clean up global listeners */
    while (!aws_linked_list_empty(&bus->global_listeners)) {
        struct aws_message_bus_listener *listener =
            AWS_CONTAINER_OF(aws_linked_list_back(&bus->global_listeners), struct aws_message_bus_listener, list_node);
        listener->deliver(0, NULL, NULL);
        aws_linked_list_pop_back(&bus->global_listeners);
    }

    /* clean up slots */
    for (size_t slot_idx = 0; slot_idx < bus->num_slots; ++slot_idx) {
        struct aws_linked_list *slot = &bus->slots[slot_idx];
        while (!aws_linked_list_empty(slot)) {
            struct aws_message_bus_listener *listener =
                AWS_CONTAINER_OF(aws_linked_list_back(slot), struct aws_message_bus_listener, list_node);
            listener->deliver(0, NULL, NULL);
            aws_linked_list_pop_back(slot);
        }
    }

    aws_mem_release(bus->allocator, bus);
}

int aws_message_bus_new_message(struct aws_message_bus *bus, size_t size, void **msg) {
    AWS_PRECONDITION(msg);
    *msg = aws_mem_acquire(bus->allocator, size);
    return AWS_OP_SUCCESS;
}

void aws_message_bus_destroy_message(struct aws_message_bus *bus, void *msg) {

}

int aws_message_bus_subscribe(struct aws_message_bus *bus, int msg_type, struct aws_message_bus_listener *listener) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_subscribe_all(struct aws_message_bus *bus, struct aws_message_bus_listener *listener) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_unsubscribe(struct aws_message_bus *bus, int msg_type, struct aws_message_bus_listener *listener) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_unsubscribe_all(struct aws_message_bus *bus, struct aws_message_bus_listener *listener) {
    return AWS_OP_SUCCESS;
}

int aws_message_bus_send(struct aws_message_bus *bus, int msg_type, void *msg) {
    return AWS_OP_SUCCESS;
}
