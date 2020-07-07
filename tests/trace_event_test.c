/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/trace_event.h>

static int s_test_trace_event(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    int b_e = 0;
    ASSERT_SUCCESS(AWS_TRACE_EVENT_INIT_(42, allocator));
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

    AWS_TRACE_EVENT_CLEAN_UP();
    return 0;
}
AWS_TEST_CASE(trace_event_test, s_test_trace_event)

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