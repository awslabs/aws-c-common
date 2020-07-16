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

static struct {
    int count;
    bool payload_deleted;
} s_sync_test;

static int s_address = 42;

static const char s_test_payload[] = "TEST ME SENPAI";

static void s_bus_sync_test_recv(uint64_t address, const void *msg, void *user_data) {
    AWS_ASSERT(s_address == address);
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

    ASSERT_SUCCESS(aws_bus_subscribe(&bus, s_address, s_bus_sync_test_recv, &s_sync_test));

    ASSERT_SUCCESS(aws_bus_send(&bus, s_address, (void *)s_test_payload, s_test_payload_dtor));

    aws_bus_unsubscribe(&bus, s_address, s_bus_sync_test_recv, &s_sync_test);

    aws_bus_clean_up(&bus);

    return 0;
}
AWS_TEST_CASE(bus_sync_test_send, s_bus_sync_test_send)

static int s_bus_sync_test_send_pod(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_bus_options options = {
        .allocator = allocator,
        .policy = AWS_BUS_SYNC,
    };

    struct aws_bus bus;
    ASSERT_SUCCESS(aws_bus_init(&bus, &options));

    aws_bus_clean_up(&bus);

    return 0;
}
AWS_TEST_CASE(bus_sync_test_send_pod, s_bus_sync_test_send_pod)

static int s_bus_async_test_send(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    return 0;
}
AWS_TEST_CASE(bus_async_test_send, s_bus_async_test_send)

static int s_bus_async_test_send_pod(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    return 0;
}
AWS_TEST_CASE(bus_async_test_send_pod, s_bus_async_test_send_pod)
