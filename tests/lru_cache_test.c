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

struct lru_test_value_element {
    bool value_removed;
};

static void s_lru_test_element_value_destroy(void *value) {
    struct lru_test_value_element *value_element = value;
    value_element->value_removed = true;
}

static int s_test_lru_cache_entries_cleanup_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lru_cache cache;

    ASSERT_SUCCESS(aws_lru_cache_init(
        &cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, s_lru_test_element_value_destroy, 2));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";

    struct lru_test_value_element first = {.value_removed = false};
    struct lru_test_value_element second = {.value_removed = false};
    struct lru_test_value_element third = {.value_removed = false};

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, second_key, &second));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, third_key, &third));
    ASSERT_INT_EQUALS(2, aws_lru_cache_get_element_count(&cache));

    ASSERT_TRUE(first.value_removed);
    ASSERT_FALSE(second.value_removed);
    ASSERT_FALSE(third.value_removed);

    struct lru_test_value_element *value = NULL;
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NULL(value);

    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_FALSE(value->value_removed);

    ASSERT_SUCCESS(aws_lru_cache_remove(&cache, second_key));
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, second_key, (void **)&value));
    ASSERT_NULL(value);
    ASSERT_TRUE(second.value_removed);

    aws_lru_cache_clear(&cache);
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, third_key, (void **)&value));
    ASSERT_NULL(value);
    ASSERT_TRUE(third.value_removed);

    aws_lru_cache_clean_up(&cache);
    return 0;
}

AWS_TEST_CASE(test_lru_cache_entries_cleanup, s_test_lru_cache_entries_cleanup_fn)

static int s_test_lru_cache_overwrite_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_lru_cache cache;

    ASSERT_SUCCESS(aws_lru_cache_init(
        &cache, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, s_lru_test_element_value_destroy, 2));

    const char *first_key = "first";

    struct lru_test_value_element first = {.value_removed = false};
    struct lru_test_value_element second = {.value_removed = false};

    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &first));
    ASSERT_SUCCESS(aws_lru_cache_put(&cache, first_key, &second));
    ASSERT_INT_EQUALS(1, aws_lru_cache_get_element_count(&cache));

    ASSERT_TRUE(first.value_removed);
    ASSERT_FALSE(second.value_removed);

    struct lru_test_value_element *value = NULL;
    ASSERT_SUCCESS(aws_lru_cache_find(&cache, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_PTR_EQUALS(&second, value);

    aws_lru_cache_clean_up(&cache);
    ASSERT_TRUE(second.value_removed);

    return 0;
}

AWS_TEST_CASE(test_lru_cache_overwrite, s_test_lru_cache_overwrite_fn)

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
