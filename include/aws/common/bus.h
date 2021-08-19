#ifndef AWS_COMMON_BUS_H
#define AWS_COMMON_BUS_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

/*
 * A message bus is a mapping of integer message addresses/types -> listeners/callbacks.
 * A listener can listen to a single message, or to all messages on a bus
 * Message addresses/types can be any 64-bit integer, starting at 1. 
 * AWS_BUS_ADDRESS_ALL (0) is reserved for broadcast to all listeners.
 * AWS_BUS_ADDRESS_CLOSE (0xffffffffffffffff) is reserved for notifying listeners to clean up
 * Listeners will be sent a message of type AWS_BUS_ADDRESS_CLOSE when it is time to clean any state up.
 * Listeners are owned by the subscriber, and are no longer referenced by the bus once unsubscribed.
 * Under the AWS_BUS_ASYNC policy, message delivery happens in a separate thread from sending, so listeners are
 * responsible for their own thread safety.
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

#define AWS_BUS_ADDRESS_ALL 0
#define AWS_BUS_ADDRESS_CLOSE ((uint64_t)-1)

struct aws_bus_options {
    enum aws_bus_policy policy;
    struct aws_allocator *allocator;
    /**
     * Size of buffer for async message queue. Messages are 40 bytes. If the queue fills, `aws_bus_send` will fail
     * Default buffer_size is 4K
     */
    size_t buffer_size;
    /* Not supported yet, but event loop group for delivery */
    struct aws_event_loop_group *event_loop_group;
};

/* Signature for listener callbacks */
typedef void(aws_bus_listener_fn)(uint64_t address, const void *payload, void *user_data);

/**
 * Initializes a message bus
 */
AWS_COMMON_API
int aws_bus_init(struct aws_bus *bus, struct aws_bus_options *options);

/**
 * Cleans up a message bus, including notifying all listeners to close
 */
AWS_COMMON_API
void aws_bus_clean_up(struct aws_bus *bus);

/**
 * Subscribes a listener to a message type
 */
AWS_COMMON_API
int aws_bus_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data);

/**
 * Unsubscribe a listener from a specific message
 */
AWS_COMMON_API
void aws_bus_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *listener, void *user_data);

/**
 * Sends a message to any listeners. payload will live until delivered, and then the destructor (if
 * provided) will be called. Note that anything payload references must also live at least until it is destroyed.
 */
AWS_COMMON_API
int aws_bus_send(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *));

#endif /* AWS_COMMON_BUS_H */
