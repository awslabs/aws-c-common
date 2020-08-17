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
#include <aws/common/byte_buf.h>
#include <aws/common/condition_variable.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/mutex.h>
#include <aws/common/ring_buffer.h>
#include <aws/common/thread.h>

#ifdef _MSC_VER
#    pragma warning(push)
#    pragma warning(disable : 4204) /* nonstandard extension used: non-constant aggregate initializer */
#endif

/* MUST be the first member of any impl to allow blind casting */
struct bus_vtable {
    void (*clean_up)(struct aws_bus *bus);
    int (*alloc)(struct aws_bus *bus, size_t size, struct aws_byte_buf *buf);
    int (*send)(struct aws_bus *bus, uint64_t address, struct aws_byte_buf payload, void (*destructor)(void *));
    int (*subscribe)(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data);
    int (*unsubscribe)(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data);
};

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
static struct listener_list *s_find_listeners(struct aws_hash_table *slots, uint64_t address) {
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
static struct listener_list *s_find_or_create_listeners(
    struct aws_allocator *allocator,
    struct aws_hash_table *slots,
    uint64_t address) {
    struct listener_list *list = s_find_listeners(slots, address);
    if (list) {
        return list;
    }

    list = aws_mem_calloc(allocator, 1, sizeof(struct listener_list));
    list->allocator = allocator;
    aws_linked_list_init(&list->listeners);
    aws_hash_table_put(slots, (void *)(uintptr_t)address, list, NULL);
    return list;
}

/* common delivery logic */
static int s_bus_deliver_msg(struct aws_bus *bus, uint64_t address, struct aws_hash_table *slots, const void *payload) {
    (void)bus;
    struct listener_list *list = s_find_listeners(slots, address);
    if (!list) {
        return AWS_OP_SUCCESS;
    }
    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners); node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        listener->deliver(address, payload, listener->user_data);
    }

    return AWS_OP_SUCCESS;
}

/* common subscribe logic */
static int s_bus_subscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {
    struct listener_list *list = s_find_or_create_listeners(bus->allocator, slots, address);
    if (!list) {
        return AWS_OP_ERR;
    }

    struct bus_listener *listener = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_listener));
    listener->deliver = callback;
    listener->user_data = user_data;
    aws_linked_list_push_back(&list->listeners, &listener->list_node);

    return AWS_OP_SUCCESS;
}

/* common unsubscribe logic */
static int s_bus_unsubscribe(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_hash_table *slots,
    aws_bus_listener_fn *callback,
    void *user_data) {
    (void)bus;

    struct listener_list *list = s_find_listeners(slots, address);
    if (!list) {
        return AWS_OP_SUCCESS;
    }

    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners); node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        if (listener->deliver == callback && listener->user_data == user_data) {
            aws_linked_list_remove(node);
            aws_mem_release(list->allocator, listener);
            break;
        }
    }

    return AWS_OP_SUCCESS;
}

/* destructor for listener lists in the slots tables */
void s_destroy_listener_list(void *data) {
    struct listener_list *list = data;
    AWS_PRECONDITION(list->allocator);
    /* call all listeners with a 0 message type to clean up */
    while (!aws_linked_list_empty(&list->listeners)) {
        struct aws_linked_list_node *back = aws_linked_list_back(&list->listeners);
        struct bus_listener *listener = AWS_CONTAINER_OF(back, struct bus_listener, list_node);
        listener->deliver(0, NULL, listener->user_data);
        aws_linked_list_pop_back(&list->listeners);
        aws_mem_release(list->allocator, listener);
    }
    aws_mem_release(list->allocator, list);
}

/*
 * AWS_BUS_SYNC implementation
 */
struct bus_sync_impl {
    struct bus_vtable vtable;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
    } slots;
    struct aws_byte_buf msg_buffer;
};

static void s_bus_sync_clean_up(struct aws_bus *bus) {
    struct bus_sync_impl *impl = bus->impl;
    aws_hash_table_clean_up(&impl->slots.table);
    aws_byte_buf_clean_up(&impl->msg_buffer);
    aws_mem_release(bus->allocator, impl);
}

static int s_bus_sync_alloc(struct aws_bus *bus, size_t size, struct aws_byte_buf *buf) {
    struct bus_sync_impl *impl = bus->impl;
    if (size > impl->msg_buffer.capacity) {
        if (aws_byte_buf_reserve(buf, size)) {
            return AWS_OP_ERR;
        }
    }

    *buf = impl->msg_buffer;
    return AWS_OP_SUCCESS;
}

static int s_bus_sync_send(
    struct aws_bus *bus,
    uint64_t address,
    struct aws_byte_buf payload,
    void (*destructor)(void *)) {
    struct bus_sync_impl *impl = bus->impl;
    int result = s_bus_deliver_msg(bus, address, &impl->slots.table, payload.buffer);
    if (destructor) {
        destructor(payload.buffer);
    } else {
        aws_byte_buf_reset(&impl->msg_buffer, false);
    }
    return result;
}

static int s_bus_sync_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_sync_impl *impl = bus->impl;
    return s_bus_subscribe(bus, address, &impl->slots.table, callback, user_data);
}

static int s_bus_sync_unsubscribe(
    struct aws_bus *bus,
    uint64_t address,
    aws_bus_listener_fn *callback,
    void *user_data) {
    struct bus_sync_impl *impl = bus->impl;
    return s_bus_unsubscribe(bus, address, &impl->slots.table, callback, user_data);
}

static struct bus_vtable s_sync_vtable = {
    .clean_up = s_bus_sync_clean_up,
    .alloc = s_bus_sync_alloc,
    .send = s_bus_sync_send,
    .subscribe = s_bus_sync_subscribe,
    .unsubscribe = s_bus_sync_unsubscribe,
};

static void *s_bus_sync_new(struct aws_bus *bus, struct aws_bus_options *options) {
    (void)options;

    struct bus_sync_impl *impl = bus->impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_sync_impl));
    if (!impl) {
        return NULL;
    }
    impl->vtable = s_sync_vtable;

    if (aws_byte_buf_init(&impl->msg_buffer, bus->allocator, 256)) {
        goto error;
    }

    if (aws_hash_table_init(
            &impl->slots.table, bus->allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_listener_list)) {
        goto error;
    }

    return impl;

error:
    aws_mem_release(bus->allocator, impl);
    return NULL;
}

/*
 * AWS_BUS_ASYNC implementation
 */
struct bus_async_impl {
    struct bus_vtable vtable;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
        struct aws_mutex mutex;
    } slots;
    /* Queue of bus_messages to deliver */
    struct {
        struct aws_ring_buffer buffer;
        struct aws_linked_list msgs;
        struct aws_mutex mutex;
    } msg_queue;

    /* consumer thread */
    struct {
        struct aws_thread thread;
        struct aws_condition_variable notify;
        bool running;
    } consumer;
};

/* represents a message in the queue on impls that queue */
struct bus_message {
    struct aws_linked_list_node list_node;
    uint64_t address;
    struct aws_byte_buf payload;
    void (*destructor)(void *);
};

static void s_bus_async_clean_up(struct aws_bus *bus) {
    struct bus_async_impl *impl = bus->impl;

    /* TODO: Tear down delivery thread */

    aws_hash_table_clean_up(&impl->slots.table);
    aws_mutex_clean_up(&impl->slots.mutex);
    aws_ring_buffer_clean_up(&impl->msg_queue.buffer);
    aws_mutex_clean_up(&impl->msg_queue.mutex);
    aws_mem_release(bus->allocator, impl);
}

static bool s_bus_async_has_data(void *user_data) {
    struct bus_async_impl *impl = user_data;
    if (!impl->consumer.running) {
        return true;
    }
    return !aws_linked_list_empty(&impl->msg_queue.msgs);
}

/* Async bus delivery thread loop */
static void s_bus_async_deliver(void *user_data) {
    struct aws_bus *bus = user_data;
    struct bus_async_impl *impl = bus->impl;

    while (impl->consumer.running) {
        if (aws_condition_variable_wait_for_pred(
                &impl->consumer.notify, &impl->msg_queue.mutex, 100, s_bus_async_has_data, impl)) {
            return;
        }

        /* Copy out the messages and dispatch them */
        struct aws_linked_list msg_list;
        aws_mutex_lock(&impl->msg_queue.mutex);
        /* BEGIN CRITICAL SECTION */
        aws_linked_list_swap_contents(&msg_list, &impl->msg_queue.msgs);
        /* END CRITICAL SECTION */
        aws_mutex_unlock(&impl->msg_queue.mutex);

        /* TODO: synchronize subscribers */
        while (!aws_linked_list_empty(&msg_list)) {
            struct aws_linked_list_node *node = aws_linked_list_front(&msg_list);
            aws_linked_list_pop_front(&msg_list);

            struct bus_message *msg = AWS_CONTAINER_OF(node, struct bus_message, list_node);
            s_bus_deliver_msg(bus, msg->address, &impl->slots.table, msg->payload.buffer);

            /* Release payload, then message queue entry */
            if (msg->destructor) {
                msg->destructor(msg->payload.buffer);
            } else {
                aws_ring_buffer_release(&impl->msg_queue.buffer, &msg->payload);
            }

            struct aws_byte_buf entry_buf = aws_byte_buf_from_array(msg, sizeof(*msg));
            aws_ring_buffer_release(&impl->msg_queue.buffer, &entry_buf);
        }
    }
}

int s_bus_async_alloc(struct aws_bus *bus, size_t size, struct aws_byte_buf *buf) {
    struct bus_async_impl *impl = bus->impl;
    return aws_ring_buffer_acquire(&impl->msg_queue.buffer, size, buf);
}

int s_bus_async_send(struct aws_bus *bus, uint64_t address, struct aws_byte_buf payload, void (*destructor)(void *)) {
    struct bus_async_impl *impl = bus->impl;

    struct aws_byte_buf entry_buf;
    AWS_ZERO_STRUCT(entry_buf);
    if (aws_ring_buffer_acquire(&impl->msg_queue.buffer, sizeof(struct bus_message), &entry_buf)) {
        return AWS_OP_ERR;
    }

    struct bus_message *msg = (struct bus_message *)entry_buf.buffer;
    msg->address = address;
    msg->payload = payload;
    msg->destructor = destructor;

    aws_mutex_lock(&impl->msg_queue.mutex);
    /* BEGIN CRITICAL SECTION */
    struct aws_linked_list *queue = &impl->msg_queue.msgs;
    aws_linked_list_push_back(queue, &msg->list_node);
    /* END CRITICAL SECTION */
    aws_mutex_unlock(&impl->msg_queue.mutex);
    return AWS_OP_SUCCESS;
}

int s_bus_async_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_async_impl *impl = bus->impl;
    aws_mutex_lock(&impl->slots.mutex);
    int result = s_bus_subscribe(bus, address, &impl->slots.table, callback, user_data);
    aws_mutex_unlock(&impl->slots.mutex);
    return result;
}

int s_bus_async_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_async_impl *impl = bus->impl;
    aws_mutex_lock(&impl->slots.mutex);
    int result = s_bus_unsubscribe(bus, address, &impl->slots.table, callback, user_data);
    aws_mutex_unlock(&impl->slots.mutex);
    return result;
}

static struct bus_vtable s_async_vtable = {
    .clean_up = s_bus_async_clean_up,
    .alloc = s_bus_async_alloc,
    .send = s_bus_async_send,
    .subscribe = s_bus_async_subscribe,
    .unsubscribe = s_bus_async_unsubscribe,
};

static void *s_bus_async_new(struct aws_bus *bus, struct aws_bus_options *options) {
    struct bus_async_impl *impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_async_impl));
    impl->vtable = s_async_vtable;

    /* init msg queue */
    if (aws_mutex_init(&impl->msg_queue.mutex)) {
        goto error;
    }
    aws_linked_list_init(&impl->msg_queue.msgs);
    if (aws_ring_buffer_init(&impl->msg_queue.buffer, bus->allocator, options->buffer_size)) {
        goto error;
    }

    /* init subscription table */
    if (aws_mutex_init(&impl->slots.mutex)) {
        goto error;
    }
    if (aws_hash_table_init(
            &impl->slots.table, bus->allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_listener_list)) {
        goto error;
    }

    /* Setup dispatch thread */
    if (aws_condition_variable_init(&impl->consumer.notify)) {
        goto error;
    }

    if (aws_thread_init(&impl->consumer.thread, bus->allocator)) {
        goto error;
    }

    impl->consumer.running = true;
    if (aws_thread_launch(&impl->consumer.thread, s_bus_async_deliver, bus, aws_default_thread_options())) {
        impl->consumer.running = false;
        goto error;
    }

    return AWS_OP_SUCCESS;

error:
    aws_thread_clean_up(&impl->consumer.thread);
    aws_condition_variable_clean_up(&impl->consumer.notify);
    aws_hash_table_clean_up(&impl->slots.table);
    aws_mutex_clean_up(&impl->slots.mutex);
    aws_ring_buffer_clean_up(&impl->msg_queue.buffer);
    aws_mutex_clean_up(&impl->msg_queue.mutex);

    aws_mem_release(bus->allocator, impl);
    return NULL;
}

/*
 * Public API
 */
int aws_bus_init(struct aws_bus *bus, struct aws_bus_options *options) {
    bus->allocator = options->allocator;
    if (options->policy == AWS_BUS_ASYNC) {

        bus->impl = s_bus_async_new(bus, options);
    } else if (options->policy == AWS_BUS_SYNC) {
        bus->impl = s_bus_sync_new(bus, options);
    }

    if (!bus->impl) {

        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_bus_clean_up(struct aws_bus *bus) {
    struct bus_vtable *vtable = bus->impl;
    vtable->clean_up(bus);
}

int aws_bus_subscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_vtable *vtable = bus->impl;
    return vtable->subscribe(bus, address, callback, user_data);
}

void aws_bus_unsubscribe(struct aws_bus *bus, uint64_t address, aws_bus_listener_fn *callback, void *user_data) {
    struct bus_vtable *vtable = bus->impl;
    vtable->unsubscribe(bus, address, callback, user_data);
}

int aws_bus_send_pod(struct aws_bus *bus, uint64_t address, struct aws_byte_cursor payload) {
    struct bus_vtable *vtable = bus->impl;
    struct aws_byte_buf payload_buf;
    AWS_ZERO_STRUCT(payload_buf);
    if (vtable->alloc(bus, payload.len, &payload_buf)) {
        return AWS_OP_ERR;
    }
    aws_byte_buf_write_from_whole_cursor(&payload_buf, payload);
    return vtable->send(bus, address, payload_buf, NULL);
}

int aws_bus_send(struct aws_bus *bus, uint64_t address, void *payload, void (*destructor)(void *)) {
    struct bus_vtable *vtable = bus->impl;
    struct aws_byte_buf payload_buf = {
        .buffer = payload,
    };
    return vtable->send(bus, address, payload_buf, destructor);
}

#ifdef _MSC_VER
#    pragma warning(pop)
#endif
