/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/trace_event.h>

#include <aws/common/thread.h>

#include <aws/common/process.h>

static int s_test_trace_event_duration(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    ASSERT_SUCCESS(aws_trace_system_init(allocator, NULL));
    AWS_TRACE_EVENT_BEGIN("TEST_CATEGORY", "TEST");

    AWS_TRACE_EVENT_END("TEST_CATEGORY", "TEST");
    aws_trace_system_clean_up();
    return 0;
}

static int s_test_trace_event_instant(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    ASSERT_SUCCESS(aws_trace_system_init(allocator, NULL));
    AWS_TRACE_EVENT_INSTANT("TEST_INSTANT", "TEST1");

    AWS_TRACE_EVENT_INSTANT("TEST_INSTANT", "TEST2");

    aws_trace_system_clean_up();
    return 0;
}

static int s_test_trace_event_counter(struct aws_allocator *allocator, void *ctx) {

    ASSERT_SUCCESS(aws_trace_system_init(allocator, NULL));
    int counter = 1;
    AWS_TRACE_EVENT_COUNTER1("TEST_COUNTER", "TEST1", counter);
    counter = 1111;
    AWS_TRACE_EVENT_COUNTER1("TEST_COUNTER", "TEST2", counter);

    aws_trace_system_clean_up();
    return 0;
}

AWS_TEST_CASE(trace_event_duration_test, s_test_trace_event_duration)

AWS_TEST_CASE(trace_event_instant_test, s_test_trace_event_instant)

AWS_TEST_CASE(trace_event_counter_test, s_test_trace_event_counter)
/*
 * figuring out unit testing
 * Should I use valgrind to check
 * use allocator in testing stuff
 * get the stuff to run and check if there are leaks using the testing framework
 * start a test that starts it up and makes sure it doesnt leak or crash
 * in terms of finding the leaks, valgrind could work for it.
 * my direction from here:
 *
 * 1. look at a bunch of traces, write up a design document (intern thing) check embark,
 * 2. test stuff then start marking up major flows of all our our code to check how time is being spent by functions
 * 3. hands on code walkthrough with the macros, code review and check style guides on aws-c-common
 * 4.
 */