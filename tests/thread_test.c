/*
 *  Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License").
 *  You may not use this file except in compliance with the License.
 *  A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 *  or in the "license" file accompanying this file. This file is distributed
 *  on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 *  express or implied. See the License for the specific language governing
 *  permissions and limitations under the License.
 */

#include <aws/common/thread.h>
#include <aws_test_harness.h>

struct thread_test_data {
    uint64_t thread_id;
};

static void thread_fn(void *arg) {
    struct thread_test_data *test_data = (struct thread_test_data *)arg;
    test_data->thread_id = aws_thread_current_thread_id();
}

static int test_thread_creation_fn(struct aws_allocator *allocator, void *ctx) {
    struct thread_test_data test_data;
    test_data.thread_id = 0;

    struct aws_thread thread;
    aws_thread_init(&thread, allocator);

    ASSERT_SUCCESS(aws_thread_create(&thread, thread_fn, (void *)&test_data, 0), "thread creation failed");
    uint64_t thread_id = aws_thread_get_id(&thread);

    ASSERT_SUCCESS(aws_thread_join(&thread), "thread join failed");

    ASSERT_INT_EQUALS(test_data.thread_id, thread_id, "get_thread_id should have returned the same id as the thread calling current_thread_id");
    aws_thread_clean_up(&thread);

    return 0;
}

AWS_TEST_CASE(thread_creation_test, test_thread_creation_fn)
