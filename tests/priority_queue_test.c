/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/priority_queue.h>
#include <aws/testing/aws_test_harness.h>
#include <stdlib.h>

static int s_compare_ints(const void *a, const void *b) {
    int arg1 = *(const int *)a;
    int arg2 = *(const int *)b;

    if (arg1 < arg2)
        return -1;
    if (arg1 > arg2)
        return 1;
    return 0;
}

static int s_test_priority_queue_preserves_order(struct aws_allocator *alloc, void *ctx) {
    struct aws_priority_queue queue;

    int err = aws_priority_queue_dynamic_init(&queue, alloc, 10, sizeof(int), s_compare_ints);
    ASSERT_SUCCESS(err, "Priority queue initialization failed with error %d", err);

    int first = 45, second = 67, third = 80, fourth = 120, fifth = 10000;

    ASSERT_SUCCESS(aws_priority_queue_push(&queue, &third), "Push operation failed for item %d", third);
    ASSERT_SUCCESS(aws_priority_queue_push(&queue, &fourth), "Push operation failed for item %d", fourth);
    ASSERT_SUCCESS(aws_priority_queue_push(&queue, &second), "Push operation failed for item %d", second);
    ASSERT_SUCCESS(aws_priority_queue_push(&queue, &fifth), "Push operation failed for item %d", fifth);
    ASSERT_SUCCESS(aws_priority_queue_push(&queue, &first), "Push operation failed for item %d", first);

    size_t num_elements = aws_priority_queue_size(&queue);
    ASSERT_INT_EQUALS(5, num_elements, "Priority queue size should have been %d but was %d", 5, num_elements);

    int pop_val, top_val, *top_val_ptr;
    err = aws_priority_queue_top(&queue, (void **)&top_val_ptr);
    ASSERT_SUCCESS(err, "Top operation failed with error %d", err);
    top_val = *top_val_ptr;
    err = aws_priority_queue_pop(&queue, &pop_val);
    ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
    ASSERT_INT_EQUALS(first, pop_val, "First element returned should have been %d but was %d", first, pop_val);
    ASSERT_INT_EQUALS(
        pop_val, top_val, "Popped element should have been the top element. expected %d but was %d", pop_val, top_val);

    err = aws_priority_queue_top(&queue, (void **)&top_val_ptr);
    ASSERT_SUCCESS(err, "Top operation failed with error %d", err);
    top_val = *top_val_ptr;
    err = aws_priority_queue_pop(&queue, &pop_val);
    ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
    ASSERT_INT_EQUALS(second, pop_val, "Second element returned should have been %d but was %d", second, pop_val);
    ASSERT_INT_EQUALS(
        pop_val, top_val, "Popped element should have been the top element. expected %d but was %d", pop_val, top_val);

    err = aws_priority_queue_top(&queue, (void **)&top_val_ptr);
    ASSERT_SUCCESS(err, "Top operation failed with error %d", err);
    top_val = *top_val_ptr;
    err = aws_priority_queue_pop(&queue, &pop_val);
    ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
    ASSERT_INT_EQUALS(third, pop_val, "Third element returned should have been %d but was %d", third, pop_val);
    ASSERT_INT_EQUALS(
        pop_val, top_val, "Popped element should have been the top element. expected %d but was %d", pop_val, top_val);

    err = aws_priority_queue_top(&queue, (void **)&top_val_ptr);
    ASSERT_SUCCESS(err, "Top operation failed with error %d", err);
    top_val = *top_val_ptr;
    err = aws_priority_queue_pop(&queue, &pop_val);
    ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
    ASSERT_INT_EQUALS(fourth, pop_val, "Fourth element returned should have been %d but was %d", fourth, pop_val);
    ASSERT_INT_EQUALS(
        pop_val, top_val, "Popped element should have been the top element. expected %d but was %d", pop_val, top_val);

    err = aws_priority_queue_top(&queue, (void **)&top_val_ptr);
    ASSERT_SUCCESS(err, "Top operation failed with error %d", err);
    top_val = *top_val_ptr;
    err = aws_priority_queue_pop(&queue, &pop_val);
    ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
    ASSERT_INT_EQUALS(fifth, pop_val, "Fifth element returned should have been %d but was %d", fifth, pop_val);
    ASSERT_INT_EQUALS(
        pop_val, top_val, "Popped element should have been the top element. expected %d but was %d", pop_val, top_val);

    ASSERT_ERROR(
        AWS_ERROR_PRIORITY_QUEUE_EMPTY,
        aws_priority_queue_pop(&queue, &pop_val),
        "Popping from empty queue should result in error");

    aws_priority_queue_clean_up(&queue);
    return 0;
}

static int s_test_priority_queue_random_values(struct aws_allocator *alloc, void *ctx) {
    enum { SIZE = 20 };
    struct aws_priority_queue queue;
    int storage[SIZE], err;
    aws_priority_queue_static_init(&queue, storage, SIZE, sizeof(int), s_compare_ints);
    int values[SIZE];
    srand((unsigned)(uintptr_t)&queue);
    for (int i = 0; i < SIZE; i++) {
        values[i] = rand() % 1000;
        err = aws_priority_queue_push(&queue, &values[i]);
        ASSERT_SUCCESS(err, "Push operation failed with error %d", err);
    }

    qsort(values, SIZE, sizeof(int), s_compare_ints);

    /* pop only half */
    for (int i = 0; i < SIZE / 2; i++) {
        int top;
        err = aws_priority_queue_pop(&queue, &top);
        ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
        ASSERT_INT_EQUALS(values[i], top, "Elements priority are out of order. Expected: %d Actual %d", values[i], top);
    }

    /* push new random values in that first half*/
    for (int i = 0; i < SIZE / 2; i++) {
        values[i] = rand() % 1000;
        err = aws_priority_queue_push(&queue, &values[i]);
        ASSERT_SUCCESS(err, "Push operation failed with error %d", err);
    }

    /* sort again so we can verify correct order on pop */
    qsort(values, SIZE, sizeof(int), s_compare_ints);
    /* pop all the queue */
    for (int i = 0; i < SIZE; i++) {
        int top;
        err = aws_priority_queue_pop(&queue, &top);
        ASSERT_SUCCESS(err, "Pop operation failed with error %d", err);
        ASSERT_INT_EQUALS(values[i], top, "Elements priority are out of order. Expected: %d Actual %d", values[i], top);
    }

    aws_priority_queue_clean_up(&queue);

    return 0;
}

static int s_test_priority_queue_size_and_capacity(struct aws_allocator *alloc, void *ctx) {
    struct aws_priority_queue queue;
    int err = aws_priority_queue_dynamic_init(&queue, alloc, 5, sizeof(int), s_compare_ints);
    ASSERT_SUCCESS(err, "Dynamic init failed with error %d", err);
    size_t capacity = aws_priority_queue_capacity(&queue);
    ASSERT_INT_EQUALS(5, capacity, "Expected Capacity %d but was %d", 5, capacity);

    for (int i = 0; i < 15; i++) {
        err = aws_priority_queue_push(&queue, &i);
        ASSERT_SUCCESS(err, "Push operation failed with error %d", err);
    }

    size_t size = aws_priority_queue_size(&queue);
    ASSERT_INT_EQUALS(15, size, "Expected Size %d but was %d", 15, capacity);

    capacity = aws_priority_queue_capacity(&queue);
    ASSERT_INT_EQUALS(20, capacity, "Expected Capacity %d but was %d", 20, capacity);

    aws_priority_queue_clean_up(&queue);
    return 0;
}

AWS_TEST_CASE(priority_queue_push_pop_order_test, s_test_priority_queue_preserves_order);
AWS_TEST_CASE(priority_queue_random_values_test, s_test_priority_queue_random_values);
AWS_TEST_CASE(priority_queue_size_and_capacity_test, s_test_priority_queue_size_and_capacity);
