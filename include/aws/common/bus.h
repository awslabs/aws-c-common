#ifndef AWS_COMMON_BUS_H
#define AWS_COMMON_BUS_H

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

#include <aws/common/common.h>

/*
 * A message bus is a mapping of integer message types -> listeners/callbacks.
 * A listener can listen to a single message, or to all messages on a bus
 * Message types must be consecutive integers, starting at 1. 0 is reserved
 * for broadcast to all handlers.
 * Handlers will be sent a message of type 0, with a NULL msg_data/user_data
 * when it is time to clean any state up.
 * Listeners are owned by the subscriber, and are no longer referenced by the bus
 * once unsubscribed.
 * Message delivery happens in a separate thread from sending, so listeners are
 * responsible for their own thread safety
 */
struct aws_bus {
    struct aws_allocator *allocator;

    /* vtable and additional data structures for delivery policy */
    void *impl;
};

enum aws_bus_policy {
    /* Message delivery is queued */
    AWS_BUS_ASYNC,
    /* Message delivery is immediate */
    AWS_BUS_SYNC,
};

struct aws_bus_options {
    enum aws_bus_policy policy;
    struct aws_allocator *allocator;
    size_t buffer_size;
    struct aws_event_loop_group *event_loop_group;
};

struct aws_byte_cursor;

/* Signature for listener callbacks */
typedef void(aws_bus_listener_fn)(uint64_t address, const void *payload, void *user_data);

/* Creates and returns a new message bus */
int aws_bus_init(struct aws_bus *bus, struct aws_bus_options *options);

/* Cleans up a message bus by notifying all listeners and releasing the bus memory */
void aws_bus_clean_up(struct aws_bus *bus);

/* Subscribes a listener to a message type */
int aws_bus_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data);

/* Unsubscribe a listener from a specific message */
void aws_bus_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data);

/*
 * Sends a message to any listeners. Memory referenced by msg will be copied into a buffer,
 * and does not need to live past this call. For simple linear buffers and structs, this
 * is the fastest/easiest dispatch.
 */
int aws_bus_send_pod(struct aws_bus *bus, uint64_t address, struct aws_byte_cursor payload);

/*
 * Sends a message to any listeners. payload will live until delivered, and then the destructor (if
 * provided) will be called). Note that anything payload references must also live at least until it is destroyed.
 */
int aws_bus_send(struct aws_bus *bus, uint64_t address, void *payload, void(*destructor)(void*));

#endif /* AWS_COMMON_BUS_H */
