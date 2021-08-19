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

static struct {
    int count;
    bool payload_deleted;
} s_sync_test;

static const char s_test_payload[] = "TEST ME SENPAI";

static void s_bus_sync_test_recv(uint64_t address, const void *msg, void *user_data) {
    AWS_ASSERT(42 == address);
    AWS_ASSERT(0 == strcmp(msg, s_test_payload));
    AWS_ASSERT(&s_sync_test == user_data);
    ++s_sync_test.count;
}

static void s_test_payload_dtor(void *payload) {
    (void)payload;
    s_sync_test.payload_deleted = true;
}

static int s_bus_sync_test_send(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_SYNC,
    };

    struct aws_bus bus;
    ASSERT_SUCCESS(aws_bus_init(&bus, &options));
    AWS_ZERO_STRUCT(s_sync_test);

    ASSERT_SUCCESS(aws_bus_subscribe(&bus, 42, s_bus_sync_test_recv, &s_sync_test));
    ASSERT_SUCCESS(aws_bus_send(&bus, 42, (void *)&s_test_payload[0], s_test_payload_dtor));

    ASSERT_INT_EQUALS(1, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    /* reset test and send a bunch of events */
    AWS_ZERO_STRUCT(s_sync_test);

    const int send_count = 100;
    for (int send = 0; send < send_count; ++send) {
        ASSERT_SUCCESS(aws_bus_send(&bus, 42, (void*)&s_test_payload[0], s_test_payload_dtor));
    }

    ASSERT_INT_EQUALS(send_count, s_sync_test.count);
    ASSERT_TRUE(s_sync_test.payload_deleted);

    aws_bus_unsubscribe(&bus, 42, s_bus_sync_test_recv, &s_sync_test);
    aws_bus_clean_up(&bus);

    return 0;
}
AWS_TEST_CASE(bus_sync_test_send, s_bus_sync_test_send)


static int s_bus_async_test_lifetime(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_ASYNC,
    };

    struct aws_bus *async_bus = aws_mem_calloc(allocator, 1, sizeof(struct aws_bus));
    ASSERT_NOT_NULL(async_bus);
    AWS_ZERO_STRUCT(*async_bus);
    ASSERT_SUCCESS(aws_bus_init(async_bus, &options));
    aws_bus_clean_up(async_bus);
    aws_mem_release(allocator, async_bus);

    /* If the background thread didn't exit cleanly, there will be hangs/leaks */

    return 0;
}
AWS_TEST_CASE(bus_async_test_lifetime, s_bus_async_test_lifetime)

static struct {
    uint64_t sum;
    uint64_t expected_sum;
    struct aws_atomic_var call_count;
    struct aws_atomic_var closed;
} s_bus_async;

struct bus_async_msg {
    struct aws_allocator *allocator;
    uint64_t destination;
};

static void s_bus_async_msg_dtor(void *data) {
    struct bus_async_msg *msg = data;
    aws_mem_release(msg->allocator, msg);
}

static void s_bus_async_handle_all(uint64_t address, const void *payload, void *user_data) {
    const bool is_close = (address == AWS_BUS_ADDRESS_CLOSE) && payload == NULL;
    const bool is_wildcard = (address > 0 && address < 1024) && payload;
    const bool is_final = (address == 1024) && payload == NULL;
    AWS_ASSERT(is_wildcard || is_final || is_close);
    AWS_ASSERT(user_data == NULL);
    aws_atomic_fetch_add(&s_bus_async.call_count, (payload != NULL));
}

static void s_bus_async_handle_msg(uint64_t address, const void *payload, void *user_data) {
    const bool is_normal = (address > 0 && address < 1024 && payload);
    const bool is_close = (address == AWS_BUS_ADDRESS_CLOSE && !payload);
    AWS_ASSERT(is_normal || is_close);
    AWS_ASSERT(user_data == &s_bus_async);
    AWS_ASSERT(!payload || ((struct bus_async_msg*)payload)->destination == address);
    if (address != AWS_BUS_ADDRESS_CLOSE) {
        s_bus_async.sum += address;
    }
}

static void s_bus_async_handle_close(uint64_t address, const void *payload, void *user_data) {
    AWS_ASSERT(address == 1024 || address == AWS_BUS_ADDRESS_CLOSE);
    AWS_ASSERT(user_data == &s_bus_async);
    AWS_ASSERT(payload == NULL);

    if (address == 1024) {
        aws_atomic_store_int(&s_bus_async.closed, 1);
    }
}

static int s_bus_async_test_send_single_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    srand(1024);
    AWS_ZERO_STRUCT(s_bus_async);
    aws_atomic_init_int(&s_bus_async.call_count, 0);
    aws_atomic_init_int(&s_bus_async.closed, 0);

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_ASYNC,
        .buffer_size = 64 * 1024,
    };

    struct aws_bus *async_bus = aws_mem_calloc(allocator, 1, sizeof(struct aws_bus));
    ASSERT_NOT_NULL(async_bus);
    AWS_ZERO_STRUCT(*async_bus);
    ASSERT_SUCCESS(aws_bus_init(async_bus, &options));

    /* test sending to all, sending to a bunch of addresses, then close */
    ASSERT_SUCCESS(aws_bus_subscribe(async_bus, AWS_BUS_ADDRESS_ALL, s_bus_async_handle_all, NULL));
    for (int address = 1; address < 1024; ++address) {
        ASSERT_SUCCESS(aws_bus_subscribe(async_bus, address, s_bus_async_handle_msg, &s_bus_async));
    }
    ASSERT_SUCCESS(aws_bus_subscribe(async_bus, 1024, s_bus_async_handle_close, &s_bus_async));

    for (int send = 0; send < 1024; ++send) {
        uint64_t address = aws_max_i32(rand() % 1024, 1);
        struct bus_async_msg *msg = aws_mem_calloc(allocator, 1, sizeof(struct bus_async_msg));
        /* released in s_bus_async_msg_dtor */
        msg->allocator = allocator;
        msg->destination = address;
        s_bus_async.expected_sum += address;
        ASSERT_SUCCESS(aws_bus_send(async_bus, address, msg, s_bus_async_msg_dtor));
    }
    ASSERT_SUCCESS(aws_bus_send(async_bus, 1024, NULL, NULL));

    /* wait for all messages to be delivered */
    /* global handler should have been called exactly as many times as there were messages, not including close */
    while (aws_atomic_load_int(&s_bus_async.call_count) < 1024) {
        aws_thread_current_sleep(1000 * 1000);
    }
    while (!aws_atomic_load_int(&s_bus_async.closed)) {
        aws_thread_current_sleep(1000 * 1000);
    }

    ASSERT_INT_EQUALS(s_bus_async.expected_sum, s_bus_async.sum);

    aws_bus_clean_up(async_bus);
    aws_mem_release(allocator, async_bus);

    return 0;
}
AWS_TEST_CASE(bus_async_test_send_single_threaded, s_bus_async_test_send_single_threaded)

static struct {
    struct aws_atomic_var call_count;
    struct aws_atomic_var expected_sum;
    struct aws_atomic_var running_sum;
} s_bus_mt_data;

static void s_async_bus_producer(void *user_data) {
    struct aws_bus *bus = user_data;
    for (int send = 0; send < 1000; ++ send) {
        const uint64_t address = aws_max_i32(rand() % 1024, 1);
        struct bus_async_msg *msg = aws_mem_calloc(bus->allocator, 1, sizeof(struct bus_async_msg));
        /* released in s_bus_async_msg_dtor */
        msg->allocator = bus->allocator;
        msg->destination = address;
        aws_atomic_fetch_add(&s_bus_mt_data.expected_sum, address);
        AWS_ASSERT(AWS_OP_SUCCESS == aws_bus_send(bus, address, msg, s_bus_async_msg_dtor));
    }
}

static void s_record_call_count(uint64_t address, const void *payload, void *user_data) {
    if (address == AWS_BUS_ADDRESS_CLOSE) {
        return;
    }
    aws_atomic_fetch_add(&s_bus_mt_data.call_count, 1);
}

static void s_address_to_running_sum(uint64_t address, const void* payload, void *user_data) {
    if (address == AWS_BUS_ADDRESS_CLOSE) {
        return;
    }
    aws_atomic_fetch_add(&s_bus_mt_data.running_sum, address);
}

static int s_bus_async_test_send_multi_threaded(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    srand(4096);

    aws_atomic_init_int(&s_bus_mt_data.call_count, 0);
    aws_atomic_init_int(&s_bus_mt_data.expected_sum, 0);
    aws_atomic_init_int(&s_bus_mt_data.running_sum, 0);

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_ASYNC,
        .buffer_size = 512 * 1024,
    };

    struct aws_bus *bus = aws_mem_calloc(allocator, 1, sizeof(struct aws_bus));
    ASSERT_NOT_NULL(bus);
    AWS_ZERO_STRUCT(*bus);
    ASSERT_SUCCESS(aws_bus_init(bus, &options));

    /* test sending to all, sending to a bunch of addresses, then close */
    ASSERT_SUCCESS(aws_bus_subscribe(bus, AWS_BUS_ADDRESS_ALL, s_record_call_count, NULL));
    for (int address = 1; address < 1024; ++address) {
        ASSERT_SUCCESS(aws_bus_subscribe(bus, address, s_address_to_running_sum, &s_bus_mt_data));
    }

    AWS_VARIABLE_LENGTH_ARRAY(struct aws_thread, threads, 8);
    for (int t = 0; t < AWS_ARRAY_SIZE(threads); ++t) {
        aws_thread_init(&threads[t], allocator);
        ASSERT_SUCCESS(aws_thread_launch(&threads[t], s_async_bus_producer, bus, aws_default_thread_options()));
    }

    /* wait for all of the wildcard messages to be delivered */
    while (aws_atomic_load_int(&s_bus_mt_data.call_count) < AWS_ARRAY_SIZE(threads) * 1000) {
        aws_thread_current_sleep(1000 * 1000);
    }

    ASSERT_INT_EQUALS(aws_atomic_load_int(&s_bus_mt_data.expected_sum), aws_atomic_load_int(&s_bus_mt_data.running_sum));
    ASSERT_INT_EQUALS(AWS_ARRAY_SIZE(threads) * 1000, aws_atomic_load_int(&s_bus_mt_data.call_count));

    aws_bus_clean_up(bus);
    aws_mem_release(allocator, bus);

    return 0;
}
AWS_TEST_CASE(bus_async_test_send_multi_threaded, s_bus_async_test_send_multi_threaded)
