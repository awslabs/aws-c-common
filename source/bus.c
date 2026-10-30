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

#include <aws/common/bus.h>

#include <aws/common/allocator.h>
#include <aws/common/atomics.h>
#include <aws/common/byte_buf.h>
#include <aws/common/condition_variable.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/logging.h>
#include <aws/common/mutex.h>
#include <aws/common/thread.h>

#include <inttypes.h>

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4204) /* nonstandard extension used: non-constant aggregate initializer */
#endif

#define AWS_BUS_DEFAULT_UNRELIABLE_BUFFER_SIZE 4096

struct bus_vtable {
    void (*destroy)(struct aws_bus *bus);

    int (*publish)(struct aws_bus *bus, const struct aws_bus_publish_options *options);

    int (*subscribe)(struct aws_bus *bus, const struct aws_bus_subscribe_options *options);

    void (*unsubscribe)(struct aws_bus *bus, const struct aws_bus_unsubscribe_options *options);
};

struct aws_bus {
    struct aws_allocator *allocator;

    struct bus_vtable *vtable;

    void *impl;
};

/* MUST be the first member of any impl to allow blind casting */

/* each bound callback is stored as a bus_listener in the slots table */
struct bus_listener {
    struct aws_linked_list_node list_node;
    void *user_data;
    aws_bus_listener_fn *deliver;
};

/* value type stored in each slot in the slots table in a bus */
struct listener_list {
    struct aws_allocator *allocator;
    struct aws_linked_list listeners;
};

/* find a listener list (or NULL) by address */
static struct listener_list *s_bus_find_listeners(struct aws_hash_table *slots, uint64_t address) {
    struct aws_hash_element *elem = NULL;
    if (aws_hash_table_find(slots, (void *)(uintptr_t)address, &elem)) {
        return NULL;
    }

    if (!elem) {
        return NULL;
    }

    struct listener_list *list = elem->value;
    return list;
}

/* find a listener list by address, or create/insert/return a new one */
static struct listener_list *s_bus_find_or_create_listeners(
    struct aws_allocator *allocator,
    struct aws_hash_table *slots,
    uint64_t address) {
    struct listener_list *list = s_bus_find_listeners(slots, address);
    if (list) {
        return list;
    }

    list = aws_mem_calloc(allocator, 1, sizeof(struct listener_list));
    list->allocator = allocator;
    aws_linked_list_init(&list->listeners);
    aws_hash_table_put(slots, (void *)(uintptr_t)address, list, NULL);
    return list;
}

static void s_bus_deliver_msg_to_slot(
    struct aws_bus *bus,
    uint64_t slot,
    struct aws_hash_table *slots,
    const struct aws_bus_listener_event *event) {
    (void)bus;
    struct listener_list *list = s_bus_find_listeners(slots, slot);
    if (!list) {
        return;
    }
    struct aws_linked_list_node *node = aws_linked_list_begin(&list->listeners);
    for (; node != aws_linked_list_end(&list->listeners); node = aws_linked_list_next(node)) {
        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        listener->deliver(event, listener->user_data);
    }
}

/* common delivery logic */
static void s_bus_deliver_msg(struct aws_bus *bus, struct aws_hash_table *slots, struct aws_bus_listener_event *event) {
    s_bus_deliver_msg_to_slot(bus, AWS_BUS_ADDRESS_ALL, slots, event);
    s_bus_deliver_msg_to_slot(bus, event->address, slots, event);
}

/* common subscribe logic */
static int s_bus_subscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {

    if (address == AWS_BUS_ADDRESS_CLOSE) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_BUS, "Cannot directly subscribe to AWS_BUS_ADDRESS_CLOSE(0)");
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    struct listener_list *list = s_bus_find_or_create_listeners(bus->allocator, slots, address);
    struct bus_listener *listener = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_listener));
    listener->deliver = callback;
    listener->user_data = user_data;
    aws_linked_list_push_back(&list->listeners, &listener->list_node);

    return AWS_OP_SUCCESS;
}

/* common unsubscribe logic */
static void s_bus_unsubscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {
    (void)bus;

    if (address == AWS_BUS_ADDRESS_CLOSE) {
        AWS_LOGF_WARN(AWS_LS_COMMON_BUS, "Attempted to unsubscribe from invalid address AWS_BUS_ADDRESS_CLOSE");
        return;
    }

    struct listener_list *list = s_bus_find_listeners(slots, address);
    if (!list) {
        return;
    }

    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners); node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        if (listener->deliver == callback && listener->user_data == user_data) {
            aws_linked_list_remove(node);
            aws_mem_release(list->allocator, listener);
            return;
        }
    }
}

/* destructor for listener lists in the slots tables */
static void s_bus_destroy_listener_list(void *data) {
    struct listener_list *list = data;
    AWS_PRECONDITION(list->allocator);

    struct aws_bus_listener_event close_event = {
        .address = AWS_BUS_ADDRESS_CLOSE,
        .payload = NULL,
    };

    /* call all listeners with an AWS_BUS_ADDRESS_CLOSE message type to clean up */
    while (!aws_linked_list_empty(&list->listeners)) {
        struct aws_linked_list_node *back = aws_linked_list_back(&list->listeners);
        struct bus_listener *listener = AWS_CONTAINER_OF(back, struct bus_listener, list_node);
        listener->deliver(&close_event, listener->user_data);
        aws_linked_list_pop_back(&list->listeners);
        aws_mem_release(list->allocator, listener);
    }
    aws_mem_release(list->allocator, list);
}

/*
 * AWS_BUS_SYNC implementation
 */
struct bus_sync_impl {
    struct aws_bus base;

    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
    } slots;
};

static void s_bus_sync_destroy(struct aws_bus *bus) {
    struct bus_sync_impl *impl = bus->impl;
    aws_hash_table_clean_up(&impl->slots.table);
    aws_mem_release(bus->allocator, impl);
}

static int s_bus_sync_publish(struct aws_bus *bus, const struct aws_bus_publish_options *options) {
    struct bus_sync_impl *impl = bus->impl;

    struct aws_bus_listener_event event = {
        .address = options->address,
        .payload = options->payload,
    };
    s_bus_deliver_msg(bus, &impl->slots.table, &event);

    if (options->destructor) {
        options->destructor(options->payload);
    }
    return AWS_OP_SUCCESS;
}

static int s_bus_sync_subscribe(struct aws_bus *bus, const struct aws_bus_subscribe_options *options) {
    struct bus_sync_impl *impl = bus->impl;
    return s_bus_subscribe(bus, options->address, &impl->slots.table, options->listener_callback, options->user_data);
}

static void s_bus_sync_unsubscribe(struct aws_bus *bus, const struct aws_bus_unsubscribe_options *options) {
    struct bus_sync_impl *impl = bus->impl;
    s_bus_unsubscribe(bus, options->address, &impl->slots.table, options->listener_callback, options->user_data);
}

static struct bus_vtable bus_sync_vtable = {
    .destroy = s_bus_sync_destroy,
    .publish = s_bus_sync_publish,
    .subscribe = s_bus_sync_subscribe,
    .unsubscribe = s_bus_sync_unsubscribe,
};

struct aws_bus *aws_bus_new_sync(struct aws_allocator *allocator) {
    struct bus_sync_impl *impl = aws_mem_calloc(allocator, 1, sizeof(struct bus_sync_impl));
    impl->base.allocator = allocator;
    impl->base.vtable = &bus_sync_vtable;
    impl->base.impl = impl;

    if (aws_hash_table_init(
            &impl->slots.table, allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_bus_destroy_listener_list)) {
        goto error;
    }

    return &impl->base;

error:

    aws_mem_release(allocator, impl);

    return NULL;
}

/*
 * AWS_BUS_ASYNC implementation
 */
struct bus_async_impl {
    struct aws_bus base;

    struct aws_bus_async_options options;

    struct aws_thread thread;

    /* backing memory for the message free list */
    void *message_buffer_start;
    void *message_buffer_end; /* 1 past the end of buffer */

    struct {
        struct aws_mutex mutex;

        struct aws_condition_variable notify;

        enum aws_bus_async_state state;

        /* Map of address -> list of listeners */
        struct aws_hash_table table;

        /* message free list */
        struct aws_linked_list free; /* struct bus_message */

        /* message delivery queue */
        struct aws_linked_list msgs; /* struct bus_message */

        /* list of pending adds/removes of listeners */
        struct aws_linked_list subs; /* struct pending_listener */

    } shared_state;
};

/* represents a message in the queue on impls that queue */
struct bus_message {
    struct aws_linked_list_node list_node;
    struct aws_bus_publish_options publish_options;
};

enum aws_bus_listener_operation_type {
    AWS_BLOT_SUBSCRIBE,
    AWS_BLOT_UNSUBSCRIBE,
};

struct pending_listener_operation {
    struct aws_linked_list_node list_node;
    enum aws_bus_listener_operation_type type;
    union {
        struct aws_bus_subscribe_options subscribe_options;
        struct aws_bus_unsubscribe_options unsubscribe_options;
    } options;
};

static void s_bus_message_clean_up(struct bus_message *msg) {
    if (msg->publish_options.destructor) {
        msg->publish_options.destructor(msg->publish_options.payload);
    }
    msg->publish_options.destructor = NULL;
    msg->publish_options.payload = NULL;
}

static void s_bus_async_free_message_reliable(struct aws_bus *bus, struct bus_message *msg) {
    s_bus_message_clean_up(msg);
    aws_mem_release(bus->allocator, msg);
}

/* Assumes the caller holds the lock */
static void s_bus_async_free_message_unreliable(struct aws_bus *bus, struct bus_message *msg) {
    struct bus_async_impl *impl = bus->impl;
    s_bus_message_clean_up(msg);
    if ((void *)msg >= impl->message_buffer_start && (void *)msg < impl->message_buffer_end) {
        AWS_ZERO_STRUCT(*msg);
        aws_linked_list_push_back(&impl->shared_state.free, &msg->list_node);
        return;
    }
    aws_mem_release(bus->allocator, msg);
}

static struct bus_message *s_bus_async_alloc_message_reliable(struct aws_bus *bus) {
    return aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_message));
}

/* Assumes the caller holds the lock */
static struct bus_message *s_bus_async_alloc_message_unreliable(struct aws_bus *bus) {
    struct bus_async_impl *impl = bus->impl;

    /* try the free list first */
    if (!aws_linked_list_empty(&impl->shared_state.free)) {
        struct aws_linked_list_node *msg_node = aws_linked_list_pop_back(&impl->shared_state.free);
        struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);
        return msg;
    }

    /* unreliable will re-use the oldest message */
    if (!aws_linked_list_empty(&impl->shared_state.msgs)) {
        struct aws_linked_list_node *msg_node = aws_linked_list_pop_front(&impl->shared_state.msgs);
        struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);
        s_bus_async_free_message_unreliable(bus, msg);

        return s_bus_async_alloc_message_unreliable(bus);
    }

    return NULL;
}

/*
 * resolve all adds and removes of listeners, in FIFO order
 * NOTE: expects mutex to be held by caller
 */
static void s_bus_apply_listeners(struct aws_bus *bus, struct aws_linked_list *pending_subs) {
    struct bus_async_impl *impl = bus->impl;
    while (!aws_linked_list_empty(pending_subs)) {
        struct aws_linked_list_node *node = aws_linked_list_pop_front(pending_subs);
        struct pending_listener_operation *listener =
            AWS_CONTAINER_OF(node, struct pending_listener_operation, list_node);
        switch (listener->type) {
            case AWS_BLOT_SUBSCRIBE: {
                struct aws_bus_subscribe_options *options = &listener->options.subscribe_options;
                s_bus_subscribe(
                    bus, options->address, &impl->shared_state.table, options->listener_callback, options->user_data);
                break;
            }

            case AWS_BLOT_UNSUBSCRIBE: {
                struct aws_bus_unsubscribe_options *options = &listener->options.unsubscribe_options;
                s_bus_unsubscribe(
                    bus, options->address, &impl->shared_state.table, options->listener_callback, options->user_data);
                if (options->unsubscribe_completion) {
                    options->unsubscribe_completion(options->address, options->user_data);
                }
                break;
            }

            default:
                break;
        }

        aws_mem_release(bus->allocator, listener);
    }
}

static void s_bus_async_deliver_messages(struct aws_bus *bus, struct aws_linked_list *pending_msgs) {
    struct bus_async_impl *impl = bus->impl;
    bool reliable = impl->options.reliable;
    struct aws_linked_list_node *msg_node = aws_linked_list_begin(pending_msgs);
    for (; msg_node != aws_linked_list_end(pending_msgs); msg_node = aws_linked_list_next(msg_node)) {
        struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);

        struct aws_bus_listener_event event = {
            .address = msg->publish_options.address,
            .payload = msg->publish_options.payload,
        };
        s_bus_deliver_msg(bus, &impl->shared_state.table, &event);
    }

    if (!reliable) {
        /* push all pending messages back on the free list */
        aws_mutex_lock(&impl->shared_state.mutex);
    }

    while (!aws_linked_list_empty(pending_msgs)) {
        msg_node = aws_linked_list_pop_front(pending_msgs);
        struct bus_message *msg = AWS_CONTAINER_OF(msg_node, struct bus_message, list_node);
        if (reliable) {
            s_bus_async_free_message_reliable(bus, msg);
        } else {
            s_bus_async_free_message_unreliable(bus, msg);
        }
    }

    if (!reliable) {
        aws_mutex_unlock(&impl->shared_state.mutex);
    }
}

static void s_bus_async_clean_up_thread_fn(void *thread_data) {
    struct aws_bus *bus = thread_data;
    struct bus_async_impl *impl = bus->impl;

    /* shut down delivery thread, clean up dispatch */
    aws_mutex_lock(&impl->shared_state.mutex);
    impl->shared_state.state = AWS_BAS_SHUTTING_DOWN;
    aws_condition_variable_notify_all(&impl->shared_state.notify);
    aws_mutex_unlock(&impl->shared_state.mutex);

    aws_thread_join(&impl->thread);
    aws_thread_clean_up(&impl->thread);

    /* should be impossible for subs or msgs to remain after final drain */
    AWS_FATAL_ASSERT(aws_linked_list_empty(&impl->shared_state.msgs));
    AWS_FATAL_ASSERT(aws_linked_list_empty(&impl->shared_state.subs));

    /* this frees everything that the free/msgs lists point to */
    if (impl->message_buffer_start) {
        aws_mem_release(bus->allocator, impl->message_buffer_start);
    }

    aws_mutex_clean_up(&impl->shared_state.mutex);
    aws_condition_variable_clean_up(&impl->shared_state.notify);

    aws_hash_table_clean_up(&impl->shared_state.table);

    void (*destroy_callback_fn)(void *) = impl->options.destroy_callback_fn;
    void *destroy_callback_user_data = impl->options.callback_user_data;

    aws_mem_release(bus->allocator, impl);

    if (destroy_callback_fn) {
        destroy_callback_fn(destroy_callback_user_data);
    }
}

static void s_aws_bus_async_destroy_async(struct aws_bus *bus) {
    /*
     * It's possible that someone calls destroy from the dispatch thread of the bus (event callback).  While a terrible
     * idea, let's not deadlock or crash.  So spawn a thread to do the actual clean up.  A clone of what we do with
     * event loop group.
     */
    struct aws_thread cleanup_thread;
    AWS_ZERO_STRUCT(cleanup_thread);

    aws_thread_init(&cleanup_thread, bus->allocator);

    struct aws_thread_options thread_options = *aws_default_thread_options();
    thread_options.join_strategy = AWS_TJS_MANAGED;
    thread_options.name = aws_byte_cursor_from_c_str("AsyncBusCleanup"); /* 15 characters is max for Linux */

    aws_thread_launch(&cleanup_thread, s_bus_async_clean_up_thread_fn, bus, &thread_options);
}

static bool s_bus_async_should_wake_up(void *user_data) {
    struct bus_async_impl *impl = user_data;
    return (impl->shared_state.state == AWS_BAS_SHUTTING_DOWN) || !aws_linked_list_empty(&impl->shared_state.subs) ||
           !aws_linked_list_empty(&impl->shared_state.msgs);
}

/* Async bus delivery thread loop */
static void s_bus_async_thread_fn(void *user_data) {
    struct aws_bus *bus = user_data;
    struct bus_async_impl *impl = bus->impl;

    AWS_LOGF_DEBUG(AWS_LS_COMMON_BUS, "bus %p: delivery thread loop started", (void *)bus);

    bool done = false;
    while (!done) {
        struct aws_linked_list pending_msgs;
        aws_linked_list_init(&pending_msgs);

        struct aws_linked_list pending_subs;
        aws_linked_list_init(&pending_subs);

        aws_mutex_lock(&impl->shared_state.mutex);
        {
            aws_condition_variable_wait_pred(
                &impl->shared_state.notify, &impl->shared_state.mutex, s_bus_async_should_wake_up, impl);

            /* copy out any queued subs/unsubs */
            aws_linked_list_swap_contents(&impl->shared_state.subs, &pending_subs);
            /* copy out any queued messages */
            aws_linked_list_swap_contents(&impl->shared_state.msgs, &pending_msgs);

            done = impl->shared_state.state == AWS_BAS_SHUTTING_DOWN;
        }
        aws_mutex_unlock(&impl->shared_state.mutex);

        /* first resolve subs/unsubs */
        if (!aws_linked_list_empty(&pending_subs)) {
            s_bus_apply_listeners(bus, &pending_subs);
        }

        /* Then deliver queued messages */
        if (!aws_linked_list_empty(&pending_msgs)) {
            s_bus_async_deliver_messages(bus, &pending_msgs);
        }
    }
}

static int s_bus_async_publish_reliable(struct aws_bus *bus, const struct aws_bus_publish_options *options) {
    struct bus_async_impl *impl = bus->impl;
    int result = AWS_OP_ERR;

    struct bus_message *msg = s_bus_async_alloc_message_reliable(bus);
    msg->publish_options = *options;

    aws_mutex_lock(&impl->shared_state.mutex);
    {
        if (impl->shared_state.state == AWS_BAS_RUNNING) {

            /* push the message onto the delivery queue */
            aws_linked_list_push_back(&impl->shared_state.msgs, &msg->list_node);
            result = AWS_OP_SUCCESS;

            /* notify the delivery thread to wake up */
            aws_condition_variable_notify_one(&impl->shared_state.notify);
        } else {
            s_bus_async_free_message_reliable(bus, msg);
        }
    }
    aws_mutex_unlock(&impl->shared_state.mutex);

    if (result == AWS_OP_ERR) {
        AWS_LOGF_WARN(
            AWS_LS_COMMON_BUS,
            "bus %p: message sent after clean_up: address: %" PRIu64 "",
            (void *)bus,
            options->address);
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }

    return result;
}

static int s_bus_async_publish_unreliable(struct aws_bus *bus, const struct aws_bus_publish_options *options) {
    struct bus_async_impl *impl = bus->impl;
    int result = AWS_OP_ERR;

    aws_mutex_lock(&impl->shared_state.mutex);
    {
        if (impl->shared_state.state == AWS_BAS_RUNNING) {
            struct bus_message *msg = s_bus_async_alloc_message_unreliable(bus);
            if (msg) {
                msg->publish_options = *options;

                /* push the message onto the delivery queue */
                aws_linked_list_push_back(&impl->shared_state.msgs, &msg->list_node);
                result = AWS_OP_SUCCESS;

                /* notify the delivery thread to wake up */
                aws_condition_variable_notify_one(&impl->shared_state.notify);
            }
        }
    }
    aws_mutex_unlock(&impl->shared_state.mutex);

    if (result) {
        AWS_LOGF_WARN(
            AWS_LS_COMMON_BUS,
            "bus %p: message sent after clean_up: address: %" PRIu64 "",
            (void *)bus,
            options->address);
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }

    return AWS_OP_SUCCESS;
}

static int s_bus_async_subscribe(struct aws_bus *bus, const struct aws_bus_subscribe_options *options) {
    struct bus_async_impl *impl = bus->impl;

    if (options->address == AWS_BUS_ADDRESS_CLOSE) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_BUS, "Cannot subscribe to AWS_BUS_ADDRESS_CLOSE");
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    int result = AWS_OP_ERR;
    struct pending_listener_operation *sub =
        aws_mem_calloc(bus->allocator, 1, sizeof(struct pending_listener_operation));
    sub->type = AWS_BLOT_SUBSCRIBE;
    sub->options.subscribe_options = *options;

    aws_mutex_lock(&impl->shared_state.mutex);
    {
        if (impl->shared_state.state == AWS_BAS_RUNNING) {
            aws_linked_list_push_back(&impl->shared_state.subs, &sub->list_node);
            result = AWS_OP_SUCCESS;

            /* notify the delivery thread to wake up */
            aws_condition_variable_notify_one(&impl->shared_state.notify);
        }
    }
    aws_mutex_unlock(&impl->shared_state.mutex);

    if (result) {
        aws_mem_release(bus->allocator, sub);
        AWS_LOGF_WARN(
            AWS_LS_COMMON_BUS,
            "bus %p: subscribe requested after clean_up: address: %" PRIu64 "",
            (void *)bus,
            options->address);
        aws_raise_error(AWS_ERROR_INVALID_STATE);
    }

    return result;
}

static void s_bus_async_unsubscribe(struct aws_bus *bus, const struct aws_bus_unsubscribe_options *options) {
    struct bus_async_impl *impl = bus->impl;

    if (options->address == AWS_BUS_ADDRESS_CLOSE) {
        AWS_LOGF_ERROR(AWS_LS_COMMON_BUS, "Cannot unsubscribe from AWS_BUS_ADDRESS_CLOSE");
        return;
    }

    int result = AWS_OP_ERR;
    struct pending_listener_operation *unsub =
        aws_mem_calloc(bus->allocator, 1, sizeof(struct pending_listener_operation));
    unsub->type = AWS_BLOT_UNSUBSCRIBE;
    ;
    unsub->options.unsubscribe_options = *options;

    aws_mutex_lock(&impl->shared_state.mutex);
    {
        if (impl->shared_state.state == AWS_BAS_RUNNING) {
            result = AWS_OP_SUCCESS;
            aws_linked_list_push_back(&impl->shared_state.subs, &unsub->list_node);

            /* notify the delivery thread to wake up */
            aws_condition_variable_notify_one(&impl->shared_state.notify);
        }
    }
    aws_mutex_unlock(&impl->shared_state.mutex);

    if (result) {
        aws_mem_release(bus->allocator, unsub);
        AWS_LOGF_WARN(
            AWS_LS_COMMON_BUS,
            "bus %p: unsubscribe requested after clean_up: address: %" PRIu64 "",
            (void *)bus,
            options->address);
    }
}

static struct bus_vtable bus_async_reliable_vtable = {
    .destroy = s_aws_bus_async_destroy_async,
    .publish = s_bus_async_publish_reliable,
    .subscribe = s_bus_async_subscribe,
    .unsubscribe = s_bus_async_unsubscribe,
};

static struct bus_vtable bus_async_unreliable_vtable = {
    .destroy = s_aws_bus_async_destroy_async,
    .publish = s_bus_async_publish_unreliable,
    .subscribe = s_bus_async_subscribe,
    .unsubscribe = s_bus_async_unsubscribe,
};

struct aws_bus *aws_bus_new_async(struct aws_allocator *allocator, const struct aws_bus_async_options *options) {
    struct bus_async_impl *impl = aws_mem_calloc(allocator, 1, sizeof(struct bus_async_impl));
    impl->base.allocator = allocator;
    impl->base.impl = impl;

    if (options->reliable) {
        impl->base.vtable = &bus_async_reliable_vtable;
    } else {
        impl->base.vtable = &bus_async_unreliable_vtable;
    }

    impl->options = *options;

    /* init msg queue */
    if (aws_mutex_init(&impl->shared_state.mutex)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_BUS,
            "bus %p: Unable to initialize queue synchronization: %s",
            (void *)&impl->base,
            aws_error_name(aws_last_error()));
        goto error;
    }
    aws_linked_list_init(&impl->shared_state.msgs);
    aws_linked_list_init(&impl->shared_state.free);
    aws_linked_list_init(&impl->shared_state.subs);

    /* push as many bus_messages as we can into the free list from the buffer */
    if (!options->reliable) {
        size_t buffer_size = options->buffer_size;
        size_t message_count = options->buffer_size / sizeof(struct bus_message);
        if (message_count == 0) {
            buffer_size = AWS_BUS_DEFAULT_UNRELIABLE_BUFFER_SIZE;
            message_count = buffer_size / sizeof(struct bus_message);
        }

        impl->message_buffer_start = aws_mem_calloc(allocator, 1, buffer_size);
        impl->message_buffer_end = ((uint8_t *)impl->message_buffer_start) + buffer_size;

        for (size_t msg_idx = 0; msg_idx < message_count; ++msg_idx) {
            struct bus_message *msg =
                (void *)&((char *)impl->message_buffer_start)[msg_idx * sizeof(struct bus_message)];
            aws_linked_list_push_back(&impl->shared_state.free, &msg->list_node);
        }
    }

    /* init subscription table */
    if (aws_hash_table_init(
            &impl->shared_state.table, allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_bus_destroy_listener_list)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_BUS,
            "bus %p: Unable to initialize bus addressing table: %s",
            (void *)&impl->base,
            aws_error_name(aws_last_error()));
        goto error;
    }

    /* Setup dispatch thread */
    if (aws_condition_variable_init(&impl->shared_state.notify)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_BUS,
            "bus %p: Unable to initialize async notify: %s",
            (void *)&impl->base,
            aws_error_name(aws_last_error()));
        goto error;
    }

    if (aws_thread_init(&impl->thread, allocator)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_BUS,
            "bus %p: Unable to initialize background thread: %s",
            (void *)&impl->base,
            aws_error_name(aws_last_error()));
        goto error;
    }

    impl->shared_state.state = AWS_BAS_RUNNING;
    if (aws_thread_launch(&impl->thread, s_bus_async_thread_fn, &impl->base, aws_default_thread_options())) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_BUS,
            "bus %p: Unable to launch delivery thread: %s",
            (void *)&impl->base,
            aws_error_name(aws_last_error()));
        goto error;
    }

    return &impl->base;

error:
    aws_thread_clean_up(&impl->thread);
    aws_condition_variable_clean_up(&impl->shared_state.notify);
    aws_hash_table_clean_up(&impl->shared_state.table);

    if (impl->message_buffer_start != NULL) {
        aws_mem_release(allocator, impl->message_buffer_start);
    }

    aws_mutex_clean_up(&impl->shared_state.mutex);
    aws_mem_release(allocator, impl);

    return NULL;
}

/*
 * Public API
 */

void aws_bus_destroy(struct aws_bus *bus) {
    struct bus_vtable *vtable = bus->vtable;
    vtable->destroy(bus);
}

int aws_bus_subscribe(struct aws_bus *bus, const struct aws_bus_subscribe_options *options) {
    return bus->vtable->subscribe(bus, options);
}

void aws_bus_unsubscribe(struct aws_bus *bus, const struct aws_bus_unsubscribe_options *options) {
    bus->vtable->unsubscribe(bus, options);
}

int aws_bus_publish(struct aws_bus *bus, const struct aws_bus_publish_options *options) {
    return bus->vtable->publish(bus, options);
}

#ifdef _MSC_VER
#    pragma warning(pop)
#endif
