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
#include <aws/common/condition_variable.h>
#include <aws/common/byte_buf.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/message_bus.h>
#include <aws/common/mutex.h>
#include <aws/common/ring_buffer.h>
#include <aws/common/thread.h>

struct bus_vtable {
    int(*init)(struct aws_message_bus *bus);
    int(*send)(struct aws_message_bus *bus, uintptr_t address, struct aws_byte_buf *payload);
    void(*destroy)(struct aws_message_bus *bus);
};

struct bus_async_impl {
    struct bus_vtable vtable;
    /* Queue of bus_messages to deliver */
    struct {
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

struct bus_sync_impl {
    struct bus_vtable vtable;
};

struct aws_message_bus {
    struct aws_allocator *allocator;
    struct {
        /* Map of address -> list of listeners */
        struct aws_hash_table table;
        struct aws_mutex mutex;
    } slots;

    /* Storage for messages until they are delivered */
    struct aws_ring_buffer msg_buffer;

    /* vtable and additional data structures for delivery policy */
    void *impl;
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

struct bus_message {
    struct aws_linked_list_node list_node;
    uintptr_t address;
    struct aws_byte_buf payload;
};

int aws_message_bus_new_message(struct aws_message_bus *bus, size_t size, struct aws_byte_buf *msg) {
    AWS_PRECONDITION(msg);
    return aws_ring_buffer_acquire(&bus->msg_buffer, size, msg);
}

void aws_message_bus_destroy_message(struct aws_message_bus *bus, struct aws_byte_buf *msg) {
    AWS_PRECONDITION(msg);
    aws_ring_buffer_release(&bus->msg_buffer, msg);
}

int aws_message_bus_subscribe(struct aws_message_bus *bus, uintptr_t address, aws_message_bus_listener_fn *callback, void *user_data) {
    aws_mutex_lock(&bus->slots.mutex);
    /* BEGIN CRITICAL SECTION */
    struct aws_hash_element *elem = NULL;
    if (aws_hash_table_find(&bus->slots.table, (void*)address, &elem)) {
        aws_mutex_unlock(&bus->slots.mutex);
        return AWS_OP_ERR;
    }
    struct listener_list *list = NULL;
    if (elem) {
        list = elem->value;
    } else {
        list = aws_mem_calloc(bus->allocator, 1, sizeof(struct listener_list));
        list->bus = bus;
        aws_linked_list_init(&list->listeners);
    }
    struct bus_listener *listener = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_listener));
    listener->deliver = callback;
    listener->user_data = user_data;
    aws_linked_list_push_back(&list->listeners, &listener->list_node);
    /* END CRITICAL SECTION */
    aws_mutex_lock(&bus->slots.mutex);
    return AWS_OP_SUCCESS;
}

int aws_message_bus_unsubscribe(struct aws_message_bus *bus, uintptr_t address, aws_message_bus_listener_fn *callback, void *user_data) {
    aws_mutex_lock(&bus->slots.mutex);
    /* BEGIN CRITICAL SECTION */
    struct aws_hash_element *elem = NULL;
    if (aws_hash_table_find(&bus->slots.table, (void*)address, &elem)) {
        aws_mutex_unlock(&bus->slots.mutex);
        return AWS_OP_ERR;
    }
    struct listener_list *list = elem->value;
    if (!list) {
        return AWS_OP_SUCCESS;
    }

    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners);
         node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        if (listener->deliver == callback && listener->user_data == user_data) {
            aws_linked_list_remove(node);
            break;
        }
    }
    /* END CRITICAL SECTION */
    aws_mutex_lock(&bus->slots.mutex);
    return AWS_OP_SUCCESS;
}

int aws_message_bus_send_copy(struct aws_message_bus *bus, uintptr_t address, void *msg, size_t msg_len) {
    struct aws_byte_buf msg_buf;
    AWS_ZERO_STRUCT(msg_buf);
    if (aws_message_bus_new_message(bus, msg_len, &msg_buf)) {
        return AWS_OP_ERR;
    }
    return aws_message_bus_send(bus, address, &msg_buf);
}

int aws_message_bus_send(struct aws_message_bus *bus, uintptr_t address, struct aws_byte_buf *msg) {
    struct bus_vtable *vtable = bus->impl;
    return vtable->send(bus, address, msg);
}

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

static void s_bus_sync_destroy(struct aws_message_bus *bus) {
    struct bus_sync_impl *sync_impl = bus->impl;
    aws_mem_release(bus->allocator, sync_impl);
}

static int s_bus_sync_init(struct aws_message_bus *bus) {
    (void)bus;
    return AWS_OP_SUCCESS;
}

static int s_bus_deliver_msg(struct aws_message_bus *bus, uintptr_t address, struct aws_byte_buf *payload) {
    struct aws_hash_element *elem = NULL;
    if (aws_hash_table_find(&bus->slots.table, (void*)address, &elem)) {
        return AWS_OP_ERR;
    }

    if (!elem) {
        return AWS_OP_SUCCESS;
    }

    struct listener_list *list = elem->value;
    struct aws_linked_list_node *node;
    for (node = aws_linked_list_begin(&list->listeners);
         node != aws_linked_list_end(&list->listeners);
         node = aws_linked_list_next(node)) {

        struct bus_listener *listener = AWS_CONTAINER_OF(node, struct bus_listener, list_node);
        listener->deliver(address, payload, listener->user_data);
    }

    return AWS_OP_SUCCESS;
}

static int s_bus_sync_send(struct aws_message_bus *bus, uintptr_t address, struct aws_byte_buf *payload) {
    int result = s_bus_deliver_msg(bus, address, payload);
    aws_message_bus_destroy_message(bus, payload);
    return result;
}

static struct bus_vtable s_sync_vtable = {
    .init = s_bus_sync_init,
    .destroy = s_bus_sync_destroy,
    .send = s_bus_sync_send,
};

static void *s_bus_sync_new(struct aws_message_bus *bus) {
    struct bus_sync_impl *sync_impl = bus->impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_sync_impl));
    if (!sync_impl) {
        return NULL;
    }
    sync_impl->vtable = s_sync_vtable;
    return sync_impl;
}

static void s_bus_async_destroy(struct aws_message_bus *bus) {
    struct bus_async_impl *async_impl = bus->impl;
    /* TODO: Tear down delivery thread */
    aws_mutex_clean_up(&async_impl->msg_queue.mutex);
    aws_mem_release(bus->allocator, async_impl);
}

static bool s_bus_async_has_data(void *user_data) {
    struct bus_async_impl *impl = user_data;
    if (!impl->consumer.running) {
        return true;
    }
    return !aws_linked_list_empty(&impl->msg_queue.msgs);
}

static void s_bus_async_deliver(void *user_data) {
    struct aws_message_bus *bus = user_data;
    struct bus_async_impl *impl = bus->impl;

    while (impl->consumer.running) {
        if (aws_condition_variable_wait_for_pred(&impl->consumer.notify, &impl->msg_queue.mutex, 100, s_bus_async_has_data, impl)) {
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
            s_bus_deliver_msg(bus, msg->address, &msg->payload);

            /* Release payload, then message queue entry */
            aws_message_bus_destroy_message(bus, &msg->payload);
            struct aws_byte_buf entry_buf = aws_byte_buf_from_array(msg, sizeof(*msg));
            aws_ring_buffer_release(&bus->msg_buffer, &entry_buf);
        }
    }
}

int s_bus_async_init(struct aws_message_bus *bus) {
    struct bus_async_impl *impl = bus->impl;
    impl->consumer.running = true;

    if (aws_condition_variable_init(&impl->consumer.notify)) {
        goto error;
    }

    if (aws_thread_init(&impl->consumer.thread, bus->allocator)) {
        goto error;
    }

    if (aws_thread_launch(&impl->consumer.thread, s_bus_async_deliver, bus, aws_default_thread_options())) {
        goto error;
    }

    return AWS_OP_SUCCESS;

error:
    aws_thread_clean_up(&impl->consumer.thread);
    aws_condition_variable_clean_up(&impl->consumer.notify);
    return AWS_OP_ERR;
}

int s_bus_async_send(struct aws_message_bus *bus, uintptr_t address, struct aws_byte_buf *payload) {
    struct bus_async_impl *impl = bus->impl;

    struct aws_byte_buf entry_buf;
    AWS_ZERO_STRUCT(entry_buf);
    if (aws_ring_buffer_acquire(&bus->msg_buffer, sizeof(struct bus_message), &entry_buf)) {
        return AWS_OP_ERR;
    }

    struct bus_message *msg = (struct bus_message*)entry_buf.buffer;
    msg->payload = *payload;
    aws_mutex_lock(&impl->msg_queue.mutex);
    /* BEGIN CRITICAL SECTION */
    struct aws_linked_list *queue = &impl->msg_queue.msgs;
    aws_linked_list_push_back(queue, &msg->list_node);
    /* END CRITICAL SECTION */
    aws_mutex_unlock(&impl->msg_queue.mutex);
    return AWS_OP_SUCCESS;
}

static struct bus_vtable s_async_vtable = {
    .init = s_bus_async_init,
    .destroy = s_bus_async_destroy,
    .send = s_bus_async_send,
};

static void *s_bus_async_new(struct aws_message_bus *bus) {
    struct bus_async_impl *async_impl = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_async_impl));
    async_impl->vtable = s_async_vtable;
    if (aws_mutex_init(&async_impl->msg_queue.mutex)) {
        goto error;
    }
    aws_linked_list_init(&async_impl->msg_queue.msgs);
    return async_impl;

error:
    aws_mutex_clean_up(&async_impl->msg_queue.mutex);
    return NULL;
}

struct aws_message_bus *aws_message_bus_new(struct aws_allocator *allocator, size_t buffer_size, enum aws_message_bus_policy policy) {
    struct aws_message_bus *bus =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_message_bus));

    bus->allocator = allocator;
    if (aws_mutex_init(&bus->slots.mutex)) {
        goto error;
    }
    if (aws_hash_table_init(&bus->slots.table, allocator, 8, aws_hash_ptr, aws_ptr_eq, NULL, s_destroy_listener_list)) {
        goto error;
    }

    if (aws_ring_buffer_init(&bus->msg_buffer, allocator, buffer_size)) {
        goto error;
    }

    if (policy == AWS_BUS_ASYNC) {
        bus->impl = s_bus_async_new(bus);
    } else if (policy == AWS_BUS_SYNC) {
        bus->impl = s_bus_sync_new(bus);
    }

    if (!bus->impl) {
        goto error;
    }

    struct bus_vtable *vtable = bus->impl;
    if (vtable->init(bus)) {
        goto error;
    }

    return bus;

error:
    if (bus->impl) {
        ((struct bus_vtable*)bus->impl)->destroy(bus);
    }
    aws_ring_buffer_clean_up(&bus->msg_buffer);
    aws_hash_table_clean_up(&bus->slots.table);
    aws_mutex_clean_up(&bus->slots.mutex);
    aws_mem_release(allocator, bus);
    return NULL;
}

void aws_message_bus_destroy(struct aws_message_bus *bus) {
    struct bus_vtable *vtable = bus->impl;
    vtable->destroy(bus);
    /* clean up listeners */
    aws_hash_table_clean_up(&bus->slots.table);
    aws_mutex_clean_up(&bus->slots.mutex);
    aws_ring_buffer_clean_up(&bus->msg_buffer);
    aws_mem_release(bus->allocator, bus);
}
