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

#include <aws/testing/aws_test_harness.h>

#include <aws/common/bus.h>
#include <aws/common/math.h>

#include <inttypes.h>

static struct {
    int count;
    bool payload_deleted;
} s_sync_test;

static const char s_test_payload[] = "TEST ME SENPAI";

static void s_bus_sync_test_recv(const struct aws_bus_listener_event *event, void *user_data) {
    AWS_FATAL_ASSERT(42 == event->address);
    AWS_FATAL_ASSERT(0 == strcmp(event->payload, s_test_payload));
    AWS_FATAL_ASSERT(&s_sync_test == user_data);
    ++s_sync_test.count;
}

static void s_test_payload_dtor(void *payload) {
    (void)payload;
    s_sync_test.payload_deleted = true;
}

static int s_bus_sync_test_send(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus *bus = aws_bus_new_sync(allocator);
    ASSERT_NOT_NULL(bus);
    AWS_ZERO_STRUCT(s_sync_test);

    struct aws_bus_subscribe_options subscribe_options = {
        .address = 42,
        .listener_callback = s_bus_sync_test_recv,
        .user_data = &s_sync_test,
    };
    ASSERT_SUCCESS(aws_bus_subscribe(bus, &subscribe_options));

    struct aws_bus_publish_options publish_options = {
        .address = 42,
        .payload = (void *)&s_test_payload[0],
        .destructor = s_test_payload_dtor,
    };
    aws_bus_publish(bus, &publish_options);

    ASSERT_INT_EQUALS(1, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    /* reset test and send a bunch of events */
    AWS_ZERO_STRUCT(s_sync_test);

    const int send_count = 100;
    for (int send = 0; send < send_count; ++send) {
        struct aws_bus_publish_options loop_publish_options = {
            .address = 42,
            .payload = (void *)&s_test_payload[0],
            .destructor = s_test_payload_dtor,
        };
        aws_bus_publish(bus, &loop_publish_options);
    }

    ASSERT_INT_EQUALS(send_count, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    struct aws_bus_unsubscribe_options unsubscribe_options = {
        .address = 42,
        .listener_callback = s_bus_sync_test_recv,
        .user_data = &s_sync_test,
    };
    aws_bus_unsubscribe(bus, &unsubscribe_options);
    aws_bus_destroy(bus);

    return 0;
}
AWS_TEST_CASE(bus_sync_test_send, s_bus_sync_test_send)

static int s_bus_async_test_lifetime(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);

    struct aws_bus_async_options bus_options = {
        .reliable = true,
    };

    struct aws_bus *async_bus = aws_bus_new_async(allocator, &bus_options);
    ASSERT_NOT_NULL(async_bus);

    aws_bus_destroy(async_bus);

    /* If the background thread didn't exit cleanly, there will be hangs/leaks */
    aws_thread_join_all_managed();
    aws_common_library_clean_up();

    return 0;
}
AWS_TEST_CASE(bus_async_test_lifetime, s_bus_async_test_lifetime)

static struct {
    struct aws_atomic_var sum;
    struct aws_atomic_var call_count;
    struct aws_atomic_var closed;
} s_bus_async;

struct bus_async_msg {
    struct aws_allocator *allocator;
    uint64_t destination;
    bool delivered;
};

static void s_bus_async_msg_dtor(void *data) {
    struct bus_async_msg *msg = data;
    aws_mem_release(msg->allocator, msg);
}

static void s_bus_async_handle_all(const struct aws_bus_listener_event *event, void *user_data) {
    const bool is_close = (event->address == AWS_BUS_ADDRESS_CLOSE) && event->payload == NULL;
    const bool is_wildcard = (event->address > 0 && event->address < 1024) && event->payload;
    const bool is_final = (event->address == 1024) && event->payload == NULL;
    AWS_FATAL_ASSERT(is_wildcard || is_final || is_close);
    AWS_FATAL_ASSERT(user_data == NULL);
    aws_atomic_fetch_add(&s_bus_async.call_count, (event->payload != NULL));
}

static void s_bus_async_handle_msg(const struct aws_bus_listener_event *event, void *user_data) {
    const bool is_normal = (event->address > 0 && event->address < 1024 && event->payload);
    const bool is_close = (event->address == AWS_BUS_ADDRESS_CLOSE && !event->payload);
    AWS_FATAL_ASSERT(is_normal || is_close);
    AWS_FATAL_ASSERT(user_data == &s_bus_async);
    AWS_FATAL_ASSERT(!event->payload || ((struct bus_async_msg *)event->payload)->destination == event->address);
    if (event->address != AWS_BUS_ADDRESS_CLOSE) {
        aws_atomic_fetch_add(&s_bus_async.sum, (size_t)event->address);
    }
}

static void s_bus_async_handle_close(const struct aws_bus_listener_event *event, void *user_data) {
    AWS_FATAL_ASSERT(event->address == 1024 || event->address == AWS_BUS_ADDRESS_CLOSE);
    AWS_FATAL_ASSERT(user_data == &s_bus_async);
    AWS_FATAL_ASSERT(event->payload == NULL);

    if (event->address == 1024) {
        aws_atomic_store_int(&s_bus_async.closed, 1);
    }
}

static int s_bus_async_test_send_single_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);

    srand(1024);
    AWS_ZERO_STRUCT(s_bus_async);
    aws_atomic_init_int(&s_bus_async.call_count, 0);
    aws_atomic_init_int(&s_bus_async.closed, 0);

    struct aws_bus_async_options options = {
        .reliable = true,
        .buffer_size = 64 * 1024,
    };

    struct aws_bus *async_bus = aws_bus_new_async(allocator, &options);
    ASSERT_NOT_NULL(async_bus);

    /* test sending to all, sending to a bunch of addresses, then close */
    struct aws_bus_subscribe_options subscribe_all_options = {
        .address = AWS_BUS_ADDRESS_ALL,
        .listener_callback = s_bus_async_handle_all,
        .user_data = NULL,
    };
    ASSERT_SUCCESS(aws_bus_subscribe(async_bus, &subscribe_all_options));

    for (int address = 1; address < 1024; ++address) {
        struct aws_bus_subscribe_options subscribe_i_options = {
            .address = address, .listener_callback = s_bus_async_handle_msg, .user_data = &s_bus_async};
        ASSERT_SUCCESS(aws_bus_subscribe(async_bus, &subscribe_i_options));
    }

    struct aws_bus_subscribe_options subscribe_close_options = {
        .address = 1024,
        .listener_callback = s_bus_async_handle_close,
        .user_data = &s_bus_async,
    };
    ASSERT_SUCCESS(aws_bus_subscribe(async_bus, &subscribe_close_options));

    uint64_t expected_sum = 0;
    for (int send = 0; send < 1024; ++send) {
        uint64_t address = aws_max_i32(rand() % 1024, 1);
        struct bus_async_msg *msg = aws_mem_calloc(allocator, 1, sizeof(struct bus_async_msg));
        /* released in s_bus_async_msg_dtor */
        msg->allocator = allocator;
        msg->destination = address;
        expected_sum += address;

        struct aws_bus_publish_options publish_options = {
            .address = address,
            .payload = msg,
            .destructor = s_bus_async_msg_dtor,
        };
        aws_bus_publish(async_bus, &publish_options);
    }

    struct aws_bus_publish_options last_publish_options = {
        .address = 1024,
        .payload = NULL,
        .destructor = NULL,
    };
    aws_bus_publish(async_bus, &last_publish_options);

    /* wait for all messages to be delivered */
    /* global handler should have been called exactly as many times as there were messages, not including close */
    while (aws_atomic_load_int(&s_bus_async.call_count) < 1024) {
        aws_thread_current_sleep(1000 * 1000);
    }
    while (!aws_atomic_load_int(&s_bus_async.closed)) {
        aws_thread_current_sleep(1000 * 1000);
    }

    size_t sum = aws_atomic_load_int(&s_bus_async.sum);
    ASSERT_INT_EQUALS(expected_sum, (uint64_t)sum);

    aws_bus_destroy(async_bus);

    aws_thread_join_all_managed();
    aws_common_library_clean_up();

    return 0;
}
AWS_TEST_CASE(bus_async_test_send_single_threaded, s_bus_async_test_send_single_threaded)

static struct {
    struct aws_atomic_var call_count;
    struct aws_atomic_var expected_sum;
    struct aws_atomic_var running_sum;
} s_bus_mt_data;

struct bus_test_ctx {
    struct aws_bus *bus;
    struct aws_allocator *allocator;
};

static void s_async_bus_producer(void *user_data) {
    struct bus_test_ctx *ctx = user_data;
    for (int send = 0; send < 1000; ++send) {
        const uint64_t address = aws_max_i32(rand() % 1024, 1);
        struct bus_async_msg *msg = aws_mem_calloc(ctx->allocator, 1, sizeof(struct bus_async_msg));
        /* released in s_bus_async_msg_dtor */
        msg->allocator = ctx->allocator;
        msg->destination = address;
        aws_atomic_fetch_add(&s_bus_mt_data.expected_sum, (size_t)address);

        struct aws_bus_publish_options publish_options = {
            .address = address,
            .payload = msg,
            .destructor = s_bus_async_msg_dtor,
        };
        aws_bus_publish(ctx->bus, &publish_options);
    }
}

static void s_record_call_count(const struct aws_bus_listener_event *event, void *user_data) {
    (void)user_data;
    if (event->address == AWS_BUS_ADDRESS_CLOSE) {
        return;
    }
    aws_atomic_fetch_add(&s_bus_mt_data.call_count, 1);
}

static void s_address_to_running_sum(const struct aws_bus_listener_event *event, void *user_data) {
    (void)user_data;
    if (event->address == AWS_BUS_ADDRESS_CLOSE) {
        return;
    }
    aws_atomic_fetch_add(&s_bus_mt_data.running_sum, (size_t)event->address);
}

static int s_bus_async_test_send_multi_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);

    srand(4096);

    aws_atomic_init_int(&s_bus_mt_data.call_count, 0);
    aws_atomic_init_int(&s_bus_mt_data.expected_sum, 0);
    aws_atomic_init_int(&s_bus_mt_data.running_sum, 0);

    struct aws_bus_async_options options = {
        .reliable = true,
        .buffer_size = 512 * 1024,
    };

    struct aws_bus *bus = aws_bus_new_async(allocator, &options);
    ASSERT_NOT_NULL(bus);

    struct aws_bus_subscribe_options subscribe_all_options = {
        .address = AWS_BUS_ADDRESS_ALL,
        .listener_callback = s_record_call_count,
        .user_data = NULL,
    };
    ASSERT_SUCCESS(aws_bus_subscribe(bus, &subscribe_all_options));
    for (int address = 1; address < 1024; ++address) {
        struct aws_bus_subscribe_options subscribe_options = {
            .address = address,
            .listener_callback = s_address_to_running_sum,
            .user_data = &s_bus_mt_data,
        };
        ASSERT_SUCCESS(aws_bus_subscribe(bus, &subscribe_options));
    }

    /* test sending to a bunch of addresses from many threads */
    struct bus_test_ctx thread_ctx = {
        .bus = bus,
        .allocator = allocator,
    };
    AWS_VARIABLE_LENGTH_ARRAY(struct aws_thread, threads, 8);
    for (int t = 0; t < AWS_ARRAY_SIZE(threads); ++t) {
        aws_thread_init(&threads[t], allocator);
        ASSERT_SUCCESS(aws_thread_launch(&threads[t], s_async_bus_producer, &thread_ctx, aws_default_thread_options()));
    }

    /* wait for all of the wildcard messages to be delivered */
    while (aws_atomic_load_int(&s_bus_mt_data.call_count) < AWS_ARRAY_SIZE(threads) * 1000) {
        aws_thread_current_sleep(1000 * 1000);
    }

    for (int t = 0; t < AWS_ARRAY_SIZE(threads); ++t) {
        aws_thread_join(&threads[t]);
        aws_thread_clean_up(&threads[t]);
    }

    ASSERT_INT_EQUALS(
        aws_atomic_load_int(&s_bus_mt_data.expected_sum), aws_atomic_load_int(&s_bus_mt_data.running_sum));
    ASSERT_INT_EQUALS(AWS_ARRAY_SIZE(threads) * 1000, aws_atomic_load_int(&s_bus_mt_data.call_count));

    aws_bus_destroy(bus);

    aws_thread_join_all_managed();
    aws_common_library_clean_up();

    return 0;
}
AWS_TEST_CASE(bus_async_test_send_multi_threaded, s_bus_async_test_send_multi_threaded)

struct {
    struct aws_atomic_var recv_count;
    struct aws_atomic_var fail_count;
    struct aws_atomic_var send_success_count;
    struct aws_atomic_var send_attempt_count;
    struct aws_atomic_var send_failure_count;
} s_bus_async_churn_data;

static void s_bus_async_test_churn_listener(const struct aws_bus_listener_event *event, void *user_data) {
    (void)user_data;
    if (event->address == AWS_BUS_ADDRESS_CLOSE) {
        return;
    }
    struct bus_async_msg *msg = (void *)event->payload;
    msg->delivered = true;
    aws_atomic_fetch_add(&s_bus_async_churn_data.recv_count, 1);
}

/* Record that message was not delivered */
static void s_bus_async_test_churn_msg_dtor(void *data) {
    struct bus_async_msg *msg = data;
    aws_atomic_fetch_add(&s_bus_async_churn_data.fail_count, (msg->delivered) ? 0 : 1);
    s_bus_async_msg_dtor(data);
}

/* This listener isn't important, it just gets randomly added/removed during churn */
static void s_bus_async_test_churn_dummy_listener(const struct aws_bus_listener_event *event, void *user_data) {
    (void)event;
    (void)user_data;
}

struct producer_data {
    struct aws_bus *bus;
    struct aws_allocator *allocator;
    int index;
    struct aws_atomic_var started;
    struct aws_atomic_var finished;
};

static void s_bus_async_test_churn_worker(void *user_data) {
    struct producer_data *producer = user_data;
    struct aws_bus *bus = producer->bus;

    aws_atomic_store_int(&producer->started, 1);
    AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Producer thread %d starting", producer->index);

    for (int send = 0; send < 10000; ++send) {
        const uint64_t address = aws_max_i32(rand() % 1024, 1);
        const int roll = (rand() % 10);
        if (roll == 0) {
            struct aws_bus_unsubscribe_options unsubscribe_options = {
                .address = address,
                .listener_callback = s_bus_async_test_churn_dummy_listener,
                .user_data = NULL,
            };
            aws_bus_unsubscribe(bus, &unsubscribe_options);
        } else if (roll < 8) {
            struct bus_async_msg *msg = aws_mem_calloc(producer->allocator, 1, sizeof(struct bus_async_msg));
            /* released in s_bus_async_msg_dtor */
            msg->allocator = producer->allocator;
            msg->destination = address;

            struct aws_bus_publish_options publish_options = {
                .address = address,
                .payload = msg,
                .destructor = s_bus_async_test_churn_msg_dtor,
            };
            // it is technically possible to fail to send because all messages might
            // be captured within the delivery loop temporarily
            bool sent = aws_bus_publish(bus, &publish_options) == AWS_OP_SUCCESS;
            aws_atomic_fetch_add(&s_bus_async_churn_data.send_attempt_count, 1);
            if (sent) {
                aws_atomic_fetch_add(&s_bus_async_churn_data.send_success_count, 1);
            } else {
                aws_atomic_fetch_add(&s_bus_async_churn_data.send_failure_count, 1);
            }
        } else {
            struct aws_bus_subscribe_options subscribe_options = {
                .address = address,
                .listener_callback = s_bus_async_test_churn_dummy_listener,
                .user_data = NULL,
            };
            aws_bus_subscribe(bus, &subscribe_options);
        }
    }

    aws_atomic_store_int(&producer->finished, 1);
    AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Producer thread %d finished", producer->index);
}

/* test subscribing, unsubscribing, sending, all from any thread on an unreliable bus */
static int s_bus_async_test_churn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);

    const uint64_t wait_ns = 15 * 1000 * 1000; /* 15 ms */

    aws_atomic_init_int(&s_bus_async_churn_data.recv_count, 0);
    aws_atomic_init_int(&s_bus_async_churn_data.send_attempt_count, 0);
    aws_atomic_init_int(&s_bus_async_churn_data.send_success_count, 0);
    aws_atomic_init_int(&s_bus_async_churn_data.send_failure_count, 0);
    aws_atomic_init_int(&s_bus_async_churn_data.fail_count, 0);

    struct aws_bus_async_options options = {
        .reliable = false,
        .buffer_size = 1024 * 1024,
    };

    struct aws_bus *bus = aws_bus_new_async(allocator, &options);
    ASSERT_NOT_NULL(bus);

    /* count all messages sent on all addresses */
    for (int address = 1; address < 1024; ++address) {
        struct aws_bus_subscribe_options subscribe_options = {
            .address = address,
            .listener_callback = s_bus_async_test_churn_listener,
            .user_data = NULL,
        };
        ASSERT_SUCCESS(aws_bus_subscribe(bus, &subscribe_options));
    }

    /* test sending to a bunch of addresses from many threads */
    struct aws_thread threads[8];
    struct producer_data thread_data[AWS_ARRAY_SIZE(threads)];
    const int num_threads = AWS_ARRAY_SIZE(threads);
    for (int t = 0; t < num_threads; ++t) {
        aws_thread_init(&threads[t], allocator);
        struct producer_data *producer = &thread_data[t];
        producer->bus = bus;
        producer->allocator = allocator;
        producer->index = t;
        aws_atomic_store_int(&producer->started, 0);
        aws_atomic_init_int(&producer->finished, 0);
        AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Launching producer thread %d", t);
        ASSERT_SUCCESS(aws_thread_launch(
            &threads[t], s_bus_async_test_churn_worker, &thread_data[t], aws_default_thread_options()));
    }

    for (int t = 0; t < num_threads; ++t) {
        struct producer_data *producer = &thread_data[t];
        while (!aws_atomic_load_int(&producer->started)) {
            AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Waiting for producer thread %d to start", t);
            aws_thread_current_sleep(wait_ns);
        }
        AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Producer thread %d is running", t);
    }

    /* wait for all producer threads to finish sending */
    for (int t = 0; t < num_threads; ++t) {
        struct producer_data *producer = &thread_data[t];
        AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Waiting for producer thread %d to finish", t);
        while (!aws_atomic_load_int(&producer->finished)) {
            aws_thread_current_sleep(wait_ns);
        }
        AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Producer thread %d is finished", t);
    }

    for (int t = 0; t < num_threads; ++t) {
        AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Joining/cleaning up producer thread %d", t);
        aws_thread_join(&threads[t]);
        aws_thread_clean_up(&threads[t]);
    }

    AWS_LOGF_TRACE(AWS_LS_COMMON_TEST, "Cleaning up test bus");

    aws_bus_destroy(bus);

    aws_thread_join_all_managed();

    size_t recv_count = aws_atomic_load_int(&s_bus_async_churn_data.recv_count);
    size_t fail_count = aws_atomic_load_int(&s_bus_async_churn_data.fail_count);
    size_t send_attempt_count = aws_atomic_load_int(&s_bus_async_churn_data.send_attempt_count);
    size_t send_failure_count = aws_atomic_load_int(&s_bus_async_churn_data.send_failure_count);
    size_t send_success_count = aws_atomic_load_int(&s_bus_async_churn_data.send_success_count);

    AWS_LOGF_INFO(
        AWS_LS_COMMON_TEST,
        "BUS CHURN TEST: send success: %zu, send failure: %zu, recv: %zu, fail: %zu",
        send_success_count,
        send_failure_count,
        recv_count,
        fail_count);
    /* Ensure SOME messages made it */
    ASSERT_TRUE(send_success_count > 0);
    ASSERT_TRUE(recv_count > 0);
    /* ensure every send is accounted for */
    ASSERT_INT_EQUALS(send_attempt_count, send_success_count + send_failure_count);
    ASSERT_INT_EQUALS(send_success_count, recv_count + fail_count);

    aws_common_library_clean_up();

    return 0;
}
AWS_TEST_CASE(bus_async_test_churn, s_bus_async_test_churn);
