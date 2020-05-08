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

#include <aws/common/lru_cache.h>
#include <aws/common/fifo_cache.h>
#include <aws/common/lifo_cache.h>
#include <aws/testing/aws_test_harness.h>

static int s_test_lru_cache_overflow_static_members_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lru_cache cache;

    ASSERT_SUCCESS(aws_lru_cache_init(&cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";
    const char *fourth_key = "fourth";

    int first = 1;
    int second = 2;
    int third = 3;
    int fourth = 4;

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(3, aws_lru_cache_get_element_count(&cache));

    int *value = NULL;
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, fourth_key, (void **)&fourth));

    /* make sure the oldest entry was purged. Note, value should now be NULL but
     * the call succeeds. */
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NULL(value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, fourth_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(fourth, *value);

    aws_lru_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_lru_cache_overflow_static_members, s_test_lru_cache_overflow_static_members_fn)

static int s_test_lru_cache_lru_ness_static_members_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lru_cache cache;

    ASSERT_SUCCESS(aws_lru_cache_init(&cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";
    const char *fourth_key = "fourth";

    int first = 1;
    int second = 2;
    int third = 3;
    int fourth = 4;

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(3, aws_lru_cache_get_element_count(&cache));

    int *value = NULL;
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, fourth_key, (void **)&fourth));

    /* The third element is the LRU element (see above). Note, value should now
     * be NULL but the call succeeds. */
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NULL(value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, fourth_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(fourth, *value);

    aws_lru_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_lru_cache_lru_ness_static_members, s_test_lru_cache_lru_ness_static_members_fn)

static int s_test_lru_cache_element_access_members_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lru_cache cache;

    ASSERT_SUCCESS(aws_lru_cache_init(&cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    int *value = NULL;
    ASSERT_NULL(aws_lru_cache_use_lru_element(&cache));
    ASSERT_NULL(aws_lru_cache_get_mru_element(&cache));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";

    int first = 1;
    int second = 2;
    int third = 3;

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(3, aws_lru_cache_get_element_count(&cache));

    value = aws_lru_cache_get_mru_element(&cache);
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    value = aws_lru_cache_use_lru_element(&cache);
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    value = aws_lru_cache_get_mru_element(&cache);
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    aws_lru_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_lru_cache_element_access_members, s_test_lru_cache_element_access_members_fn)

static int s_test_fifo_cache_overflow_static_members_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_fifo_cache cache;

    ASSERT_SUCCESS(
        aws_fifo_cache_init(&cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";
    const char *fourth_key = "fourth";

    int first = 1;
    int second = 2;
    int third = 3;
    int fourth = 4;

    ASSERT_SUCCESS(aws_fifo_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_fifo_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_fifo_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(3, aws_fifo_cache_get_element_count(&cache));

    int *value = NULL;
    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_fifo_cache_put(&cache, fourth_key, (void **)&fourth));

    /* make sure the oldest entry was purged. Note, value should now be NULL but
     * the call succeeds. */
    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NULL(value);

    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_fifo_cache_find(&cache, fourth_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(fourth, *value);

    aws_fifo_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_fifo_cache_overflow_static_members, s_test_fifo_cache_overflow_static_members_fn)

static int s_test_lifo_cache_overflow_static_members_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lifo_cache cache;

    ASSERT_SUCCESS(
        aws_lifo_cache_init(&cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";
    const char *fourth_key = "fourth";

    int first = 1;
    int second = 2;
    int third = 3;
    int fourth = 4;

    ASSERT_SUCCESS(aws_lifo_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lifo_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_lifo_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(3, aws_lifo_cache_get_element_count(&cache));

    int *value = NULL;
    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_lifo_cache_put(&cache, fourth_key, (void **)&fourth));

    /* make sure the latest entry was purged. Note, value should now be NULL but
     * the call succeeds. */
    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NULL(value);

    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_lifo_cache_find(&cache, fourth_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(fourth, *value);

    aws_lifo_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_lifo_cache_overflow_static_members, s_test_lifo_cache_overflow_static_members_fn)
