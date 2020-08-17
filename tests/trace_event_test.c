/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/trace_event.h>

/* Unit Tests have been depricated after cJSON removal */

static int s_test_trace_event_duration(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;
    return 0;
}

static int s_test_trace_event_instant(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;
    return 0;
}

static int s_test_trace_event_counter(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    (void)allocator;
    return 0;
}

AWS_TEST_CASE(trace_event_duration_test, s_test_trace_event_duration)

AWS_TEST_CASE(trace_event_instant_test, s_test_trace_event_instant)

AWS_TEST_CASE(trace_event_counter_test, s_test_trace_event_counter)
