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
 * AWS_BUS_ADDRESS_ALL (0xffffffffffffffff) is reserved for broadcast to all listeners.
 * AWS_BUS_ADDRESS_CLOSE (0) is reserved for notifying listeners to clean up
 * Listeners will be sent a message of type AWS_BUS_ADDRESS_CLOSE when it is time to clean any state up.
 * Listeners are owned by the subscriber, and are no longer referenced by the bus once unsubscribed.
 * Under the AWS_BUS_ASYNC policy, message delivery happens in a separate thread from sending, so listeners are
 * responsible for their own thread safety.
 */
struct aws_bus;

/**
 * Current state of an async bus implementation
 */
enum aws_bus_async_state {
    AWS_BAS_INITIAL,
    AWS_BAS_RUNNING,
    AWS_BAS_SHUTTING_DOWN,
};

struct aws_bus_async_options {

    /**
     * If true, messages will be delivered, even if dynamic allocation is required.
     * If false, only memory from the bus's internal buffer will be used (if a buffer size is supplied at bus
     * creation time).  If the buffer is full, older buffered messages will be discarded to make room for newer
     * messages.
     */
    bool reliable;

    /**
     * Size of buffer for unreliable message delivery queue. Unused if reliable is true.
     * Messages are 40 bytes. Default buffer_size is 4K. The bus will not allocate memory beyond this size.
     */
    size_t buffer_size;

    /** called when the bus has been fully destroyed */
    void (*destroy_callback_fn)(void *);

    /** user data to include in callbacks */
    void *callback_user_data;
};

/**
 * Subscribing to AWS_BUS_ADDRESS_ALL will cause the listener to be invoked for every message sent to the bus
 * It is possible to send to AWS_BUS_ADDRESS_ALL, just be aware that this will only send to listeners subscribed
 * to AWS_BUS_ADDRESS_ALL.
 */
#define AWS_BUS_ADDRESS_ALL ((uint64_t) - 1)
#define AWS_BUS_ADDRESS_CLOSE 0

/**
 * Encapsulates all data about an event
 */
struct aws_bus_listener_event {

    /** Address the event was sent to */
    uint64_t address;

    /** Payload of the event */
    const void *payload;
};

/* Signature for listener callbacks */
typedef void(aws_bus_listener_fn)(const struct aws_bus_listener_event *event, void *user_data);

/* Optional callback when unsubscribe completes. Signals the listener can be safely claned up. */
typedef void(aws_bus_listener_unsubscribe_completion_fn)(uint64_t address, void *user_data);

/**
 * Options for message subscription
 */
struct aws_bus_subscribe_options {

    /** address to subscribe to */
    uint64_t address;

    /** callback to invoke on message publish */
    aws_bus_listener_fn *listener_callback;

    /** callback user data.  lifetime is the responsibility of the subscriber. */
    void *user_data;
};

/**
 * Message unsubscribe options.  Listener_fn and user_data must match an existing subscription to be successful.
 */
struct aws_bus_unsubscribe_options {

    /** Address to unsubscribe from */
    uint64_t address;

    /** Callback that was subscribed with */
    aws_bus_listener_fn *listener_callback;

    /** Optional function that will be invoked when the unsubscribe completes.  Async only.  Ignored by the sync bus
     * in order to avoid potential recursion issues.
     */
    aws_bus_listener_unsubscribe_completion_fn *unsubscribe_completion;

    /** user data that was subscribed with */
    void *user_data;
};

/**
 * Message publish options
 */
struct aws_bus_publish_options {

    /** Address to publish to */
    uint64_t address;

    /** Payload of the message. */
    void *payload;

    /** Destructor function of the payload.  Called after the message has been delivered to all subscribers */
    void (*destructor)(void *);
};

/**
 * Allocates and initializes a synchronous message bus
 */
AWS_COMMON_API
struct aws_bus *aws_bus_new_sync(struct aws_allocator *allocator);

/**
 * Allocates and initializes an asynchronous message bus
 */
AWS_COMMON_API
struct aws_bus *aws_bus_new_async(struct aws_allocator *allocator, const struct aws_bus_async_options *options);

/**
 * Cleans up a message bus, including notifying all remaining listeners to close
 */
AWS_COMMON_API
void aws_bus_destroy(struct aws_bus *bus);

/**
 * Subscribes a listener to a message type.
 */
AWS_COMMON_API
int aws_bus_subscribe(struct aws_bus *bus, const struct aws_bus_subscribe_options *options);

/**
 * Unsubscribe a listener from a specific message. This is only necessary if the listener has lifetime concerns.
 * Otherwise, the listener will be called with an address of AWS_BUS_ADDRESS_CLOSE, which indicates that user_data
 * can be cleaned up if necessary and the listener will never be called again.
 */
AWS_COMMON_API
void aws_bus_unsubscribe(struct aws_bus *bus, const struct aws_bus_unsubscribe_options *options);

/**
 * Sends a message to any listeners. payload will live until delivered, and then the destructor (if
 * provided) will be called. Note that anything payload references must also live at least until it is destroyed.
 * Will return AWS_OP_ERR if the bus is closing/has been closed
 */
AWS_COMMON_API
int aws_bus_publish(struct aws_bus *bus, const struct aws_bus_publish_options *options);

#endif /* AWS_COMMON_BUS_H */
