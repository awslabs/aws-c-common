#ifndef AWS_COMMON_MESSAGE_BUS_H
#define AWS_COMMON_MESSAGE_BUS_H

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
#include <aws/common/linked_list.h>

/*
 * A message bus is a mapping of integer message types -> listeners/callbacks.
 * A listener can listen to a single message, or to all messages on a bus
 * Message types must be consecutive integers, starting at 1. 0 is reserved
 * for broadcast to all handlers.
 * Handlers will be sent a message of type 0, with a NULL msg_data/user_data
 * when it is time to clean any state up.
 * Listeners are owned by the subscriber, and are no longer referenced by the bus
 * once unsubscribed.
 */
struct aws_message_bus;

/* Signature for listener callbacks */
typedef void(aws_message_bus_listener_fn)(int msg_type, void *msg_data, void *user_data);

struct aws_message_bus_listener {
    struct aws_linked_list_node list_node;
    void *user_data;
    aws_message_bus_listener_fn *deliver;
};

/* Creates and returns a new message bus */
struct aws_message_bus *aws_message_bus_new(struct aws_allocator *allocator, size_t slots);

/* Cleans up a message bus by notifying all listeners and releasing the bus memory */
void aws_message_bus_destroy(struct aws_message_bus *bus);

/* Subscribes a listener to a message type */
int aws_message_bus_subscribe(struct aws_message_bus *bus, int msg_type, struct aws_message_bus_listener *listener);

/* Subscribes a listener to all incoming messages */
int aws_message_bus_subscribe_all(struct aws_message_bus *bus, struct aws_message_bus_listener *listener);

/* Unsubscribes a listener from a specific message */
int aws_message_bus_unsubscribe(struct aws_message_bus *bus, int msg_type, struct aws_message_bus_listener *listener);

/* Unsubscribes a listener from all incoming messages */
int aws_message_bus_unsubscribe_all(struct aws_message_bus *bus, struct aws_message_bus_listener *listener);

/*
 * Allocates a new message to be sent. The message bus owns this memory, and is responsible
 * for freeing it when message delivery is complete. If an error occurs before the message
 * is sent, it may be freed with aws_message_bus_destroy_message()
 */
int aws_message_bus_new_message(struct aws_message_bus *bus, size_t size, void **msg);

/*
 * Frees a message buffer allocated by aws_message_bus_new_message. Only necessary if the
 * message is never sent
 */
void aws_message_bus_destroy_message(struct aws_message_bus *bus, void *msg);

/*
 * Sends a message to any listeners. msg_data should have been allocated by aws_message_bus_new_message
 * and will be cleaned up after the message is delivered
 */
int aws_message_bus_send(struct aws_message_bus *bus, int msg_type, void *msg_data);

#endif /* AWS_COMMON_MESSAGE_BUS_H */
