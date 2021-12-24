/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list_with_map.h>
#include <aws/common/string.h>

#include <aws/testing/aws_test_harness.h>

static int s_array_list_with_map_sanitize_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_array_list_with_map list_with_map;
    ASSERT_SUCCESS(
        aws_array_list_with_map_init(&list_with_map, allocator, aws_hash_ptr, aws_ptr_eq, NULL, sizeof(void *), 0));
    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_sanitize_test, s_array_list_with_map_sanitize_fn)

static int s_array_list_with_map_insert_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    AWS_STATIC_STRING_FROM_LITERAL(foo, "foo");
    AWS_STATIC_STRING_FROM_LITERAL(bar, "bar");
    AWS_STATIC_STRING_FROM_LITERAL(foobar, "foobar");

    struct aws_array_list_with_map list_with_map;
    /* With only 1 initial element. */
    ASSERT_SUCCESS(aws_array_list_with_map_init(
        &list_with_map, allocator, aws_hash_string, aws_hash_callback_string_eq, NULL, sizeof(struct aws_string), 1));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foobar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, bar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));

    /* You cannot have duplicates */
    ASSERT_FAILS(aws_array_list_with_map_insert(&list_with_map, foobar));

    /* Check the size */
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 3);

    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_insert_test, s_array_list_with_map_insert_fn)

static int s_array_list_with_map_get_random_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    AWS_STATIC_STRING_FROM_LITERAL(foo, "foo");

    struct aws_array_list_with_map list_with_map;
    /* With only 1 initial element. */
    ASSERT_SUCCESS(aws_array_list_with_map_init(
        &list_with_map, allocator, aws_hash_string, aws_hash_callback_string_eq, NULL, sizeof(struct aws_string), 1));
    struct aws_string left_element;
    /* Fail to get any, when there is nothing in it. */
    ASSERT_FAILS(aws_array_list_with_map_get_random(&list_with_map, &left_element));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));

    /* Check the size */
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 1);
    ASSERT_SUCCESS(aws_array_list_with_map_get_random(&list_with_map, &left_element));
    ASSERT_TRUE(aws_string_eq(&left_element, foo));

    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_get_random_test, s_array_list_with_map_get_random_fn)

static int s_array_list_with_map_exist_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    AWS_STATIC_STRING_FROM_LITERAL(foo, "foo");
    AWS_STATIC_STRING_FROM_LITERAL(bar, "bar");

    struct aws_array_list_with_map list_with_map;
    ASSERT_SUCCESS(aws_array_list_with_map_init(
        &list_with_map, allocator, aws_hash_string, aws_hash_callback_string_eq, NULL, sizeof(struct aws_string), 1));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));

    ASSERT_TRUE(aws_array_list_with_map_exist(&list_with_map, foo));
    ASSERT_FALSE(aws_array_list_with_map_exist(&list_with_map, bar));

    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_exist_test, s_array_list_with_map_exist_fn)

static int s_array_list_with_map_remove_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    AWS_STATIC_STRING_FROM_LITERAL(foo, "foo");
    AWS_STATIC_STRING_FROM_LITERAL(bar, "bar");
    AWS_STATIC_STRING_FROM_LITERAL(foobar, "foobar");

    struct aws_array_list_with_map list_with_map;
    /* With only 1 initial element. */
    ASSERT_SUCCESS(aws_array_list_with_map_init(
        &list_with_map, allocator, aws_hash_string, aws_hash_callback_string_eq, NULL, sizeof(struct aws_string), 1));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foobar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, bar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));

    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, foo));
    /* Check the size */
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 2);

    /* Should be fine to remove something not existing anymore? */
    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, foo));

    /* Remove all beside foobar, so, if we get one random, it will be foobar */
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foobar));
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 1);
    struct aws_string left_element;
    ASSERT_SUCCESS(aws_array_list_with_map_get_random(&list_with_map, &left_element));
    ASSERT_TRUE(aws_string_eq(&left_element, bar));

    /* Remove last thing and make sure everything should still work */
    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, bar));
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 0);
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 1);
    ASSERT_SUCCESS(aws_array_list_with_map_get_random(&list_with_map, &left_element));
    ASSERT_TRUE(aws_string_eq(&left_element, foo));

    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_remove_test, s_array_list_with_map_remove_fn)

static void s_aws_string_destroy_callback(void *key) {
    struct aws_string *str = (struct aws_string *)key;
    aws_string_destroy(str);
}

static int s_array_list_with_map_owns_element_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_string *foo = aws_string_new_from_c_str(allocator, "foo");
    struct aws_string *bar = aws_string_new_from_c_str(allocator, "bar");
    struct aws_string *foobar = aws_string_new_from_c_str(allocator, "foobar");

    struct aws_array_list_with_map list_with_map;
    /* With only 1 initial element. Add clean up for the string */
    ASSERT_SUCCESS(aws_array_list_with_map_init(
        &list_with_map,
        allocator,
        aws_hash_string,
        aws_hash_callback_string_eq,
        s_aws_string_destroy_callback,
        sizeof(struct aws_string),
        1));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foobar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, bar));
    ASSERT_SUCCESS(aws_array_list_with_map_insert(&list_with_map, foo));

    /* You cannot have duplicates */
    ASSERT_FAILS(aws_array_list_with_map_insert(&list_with_map, foobar));

    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, foo));
    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, foobar));
    ASSERT_SUCCESS(aws_array_list_with_map_remove(&list_with_map, bar));

    /* Check the size */
    ASSERT_UINT_EQUALS(aws_array_list_with_map_length(&list_with_map), 0);

    aws_array_list_with_map_clean_up(&list_with_map);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(array_list_with_map_owns_element_test, s_array_list_with_map_owns_element_fn)
