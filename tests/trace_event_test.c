/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/trace_event.h>

#include <aws/common/thread.h>

#include <aws/common/external/cJSON.h>

#include <aws/common/process.h>

static int s_test_trace_event_duration(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    int b_e = 0;
    ASSERT_SUCCESS(aws_trace_system_init(NULL, allocator));
    ASSERT_SUCCESS(AWS_TRACE_EVENT_BEGIN("TEST_CATEGORY", "TEST"));

    ASSERT_SUCCESS(AWS_TRACE_EVENT_END("TEST_CATEGORY", "TEST"));

    struct cJSON *root = (struct cJSON *)aws_trace_event_get_root();
    ASSERT_TRUE(cJSON_HasObjectItem(root, "traceEvents"));
    struct cJSON *event_array = cJSON_GetObjectItem(root, "traceEvents");
    struct cJSON *event;
    cJSON_ArrayForEach(event, event_array) {
        struct cJSON *cat = cJSON_GetObjectItem(event, "cat");
        ASSERT_INT_EQUALS(strcmp(cat->valuestring, "TEST_CATEGORY"), 0);

        struct cJSON *name = cJSON_GetObjectItem(event, "name");
        ASSERT_INT_EQUALS(strcmp(name->valuestring, "TEST"), 0);

        struct cJSON *ph = cJSON_GetObjectItem(event, "ph");
        if (!b_e) {
            ASSERT_INT_EQUALS(strcmp(ph->valuestring, "B"), 0);
            b_e += 1;
        } else {
            ASSERT_INT_EQUALS(strcmp(ph->valuestring, "E"), 0);
        }

        struct cJSON *pid = cJSON_GetObjectItem(event, "pid");
        ASSERT_INT_EQUALS(pid->valueint, aws_get_pid());

        /* This test has weird casting */
        struct cJSON *tid = cJSON_GetObjectItem(event, "tid");
        ASSERT_UINT_EQUALS((uint64_t)tid->valuedouble, (uint64_t)aws_thread_current_thread_id());
    }

    aws_trace_system_clean_up();
    return 0;
}

static int s_test_trace_event_instant(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    ASSERT_SUCCESS(aws_trace_system_init(NULL, allocator));
    ASSERT_SUCCESS(AWS_TRACE_EVENT_INSTANT("TEST_INSTANT", "TEST1"));

    ASSERT_SUCCESS(AWS_TRACE_EVENT_INSTANT("TEST_INSTANT", "TEST2"));

    struct cJSON *root = (struct cJSON *)aws_trace_event_get_root();
    ASSERT_TRUE(cJSON_HasObjectItem(root, "traceEvents"));
    struct cJSON *event_array = cJSON_GetObjectItem(root, "traceEvents");
    struct cJSON *event;
    int event_num = 0;
    cJSON_ArrayForEach(event, event_array) {
        struct cJSON *cat = cJSON_GetObjectItem(event, "cat");
        ASSERT_INT_EQUALS(strcmp(cat->valuestring, "TEST_INSTANT"), 0);

        struct cJSON *name = cJSON_GetObjectItem(event, "name");

        struct cJSON *ph = cJSON_GetObjectItem(event, "ph");
        ASSERT_INT_EQUALS(strcmp(ph->valuestring, "I"), 0);

        if (!event_num) {
            ASSERT_INT_EQUALS(strcmp(name->valuestring, "TEST1"), 0);
            event_num += 1;
        } else {
            ASSERT_INT_EQUALS(strcmp(name->valuestring, "TEST2"), 0);
        }

        struct cJSON *pid = cJSON_GetObjectItem(event, "pid");
        ASSERT_INT_EQUALS(pid->valueint, aws_get_pid());

        /* This test has weird casting */
        struct cJSON *tid = cJSON_GetObjectItem(event, "tid");
        ASSERT_UINT_EQUALS((uint64_t)tid->valuedouble, (uint64_t)aws_thread_current_thread_id());
    }

    aws_trace_system_clean_up();
    return 0;
}

static int s_test_trace_event_counter(struct aws_allocator *allocator, void *ctx) {

    ASSERT_SUCCESS(aws_trace_system_init(NULL, allocator));
    int counter = 1;
    ASSERT_SUCCESS(AWS_TRACE_EVENT_COUNTER1("TEST_COUNTER", "TEST1", counter));
    counter = 1111;
    ASSERT_SUCCESS(AWS_TRACE_EVENT_COUNTER1("TEST_COUNTER", "TEST2", counter));
    struct cJSON *root = (struct cJSON *)aws_trace_event_get_root();
    struct cJSON *event_array = cJSON_GetObjectItem(root, "traceEvents");
    struct cJSON *event;
    int event_num = 0;
    cJSON_ArrayForEach(event, event_array) {
        struct cJSON *cat = cJSON_GetObjectItem(event, "cat");
        ASSERT_INT_EQUALS(strcmp(cat->valuestring, "TEST_COUNTER"), 0);

        struct cJSON *name = cJSON_GetObjectItem(event, "name");

        struct cJSON *ph = cJSON_GetObjectItem(event, "ph");
        ASSERT_INT_EQUALS(strcmp(ph->valuestring, "C"), 0);
        struct cJSON *args = cJSON_GetObjectItem(event, "args");
        struct cJSON *event_counter = cJSON_GetObjectItem(args, "counter");
        if (!event_num) {

            ASSERT_INT_EQUALS(strcmp(name->valuestring, "TEST1"), 0);

            ASSERT_INT_EQUALS(event_counter->valueint, 1);
            event_num += 1;
        } else {
            ASSERT_INT_EQUALS(strcmp(name->valuestring, "TEST2"), 0);
            ASSERT_INT_EQUALS(event_counter->valueint, 1111);
        }

        struct cJSON *pid = cJSON_GetObjectItem(event, "pid");
        ASSERT_INT_EQUALS(pid->valueint, aws_get_pid());

        /* This test has weird casting */
        struct cJSON *tid = cJSON_GetObjectItem(event, "tid");
        ASSERT_UINT_EQUALS((uint64_t)tid->valuedouble, (uint64_t)aws_thread_current_thread_id());
    }

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