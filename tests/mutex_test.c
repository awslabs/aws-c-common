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

#include <aws/common/mutex.h>
#include <aws/common/thread.h>
#include <aws_test_harness.h>

static int test_mutex_acquire_release(struct aws_allocator *allocator, void *ctx) {
    struct aws_mutex mutex;
    aws_mutex_init(&mutex, allocator);

    ASSERT_SUCCESS(aws_mutex_acquire(&mutex), "Mutex acquire should have returned success.");
    ASSERT_SUCCESS(aws_mutex_release(&mutex),"Mutex release should have returned success.");

    aws_mutex_clean_up(&mutex);

    return 0;
}

struct thread_mutex_data {
    struct aws_mutex mutex;
    volatile int thread_1_written;
    volatile int thread_2_written;
    volatile int thread_2_detected_write_from_thread_1;
};

static void mutex_thread_fn(void *mutex_data) {
    struct thread_mutex_data *p_mutex = (struct thread_mutex_data *)mutex_data;
    while(!(p_mutex->thread_2_detected_write_from_thread_1 = p_mutex->thread_1_written)) continue;
    aws_mutex_acquire(&p_mutex->mutex);
    p_mutex->thread_2_written = 1;
    aws_mutex_release(&p_mutex->mutex);
}

static int test_mutex_is_actually_mutex(struct aws_allocator *allocator, void *ctx) {

    struct thread_mutex_data mutex_data;
    aws_mutex_init(&mutex_data.mutex, allocator);
    mutex_data.thread_1_written = 0;
    mutex_data.thread_2_written = 0;
    mutex_data.thread_2_detected_write_from_thread_1 = 0;

    ASSERT_SUCCESS(aws_mutex_acquire(&mutex_data.mutex), "mutex acquire failed with error %d", aws_last_error());

    struct aws_thread thread;
    aws_thread_init(&thread, allocator);
    ASSERT_SUCCESS(aws_thread_create(&thread, mutex_thread_fn, &mutex_data, 0), "thread creation failed with error %d", aws_last_error());

    int thread_2_wrote_first = mutex_data.thread_2_written;
    mutex_data.thread_1_written = 1;

    while (!mutex_data.thread_2_detected_write_from_thread_1) continue;
    thread_2_wrote_first |= mutex_data.thread_2_written;

    ASSERT_SUCCESS(aws_mutex_release(&mutex_data.mutex), "mutex release failed with error %d", aws_last_error());
    ASSERT_SUCCESS(aws_thread_join(&thread), "thread join failed with error %d", aws_last_error());

    ASSERT_INT_EQUALS(0, thread_2_wrote_first, "Thread 2 should have written second");
    ASSERT_INT_EQUALS(1, mutex_data.thread_1_written, "Thread 1 should have written");
    ASSERT_INT_EQUALS(1, mutex_data.thread_2_written, "Thread 2 should have written");
    ASSERT_INT_EQUALS(1, mutex_data.thread_2_detected_write_from_thread_1, "Thread 1 should have written first.");

    aws_thread_clean_up(&thread);
    aws_mutex_clean_up(&mutex_data.mutex);

    return 0;
}

AWS_TEST_CASE(mutex_aquire_release_test, test_mutex_acquire_release)
AWS_TEST_CASE(mutex_is_actually_mutex_test, test_mutex_is_actually_mutex)