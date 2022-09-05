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

#include <aws/common/linked_hash_table.h>
#include <aws/common/string.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_linked_hash_table_preserves_insertion_order_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_linked_hash_table table;

    ASSERT_SUCCESS(
        aws_linked_hash_table_init(&table, allocator, aws_hash_c_string, aws_hash_callback_c_str_eq, NULL, NULL, 3));

    const char *first_key = "first";
    const char *second_key = "second";
    const char *third_key = "third";
    const char *fourth_key = "fourth";

    int first = 1;
    int second = 2;
    int third = 3;
    int fourth = 4;

    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key, &first));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, second_key, &second));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, third_key, &third));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, fourth_key, &fourth));

    ASSERT_INT_EQUALS(4, aws_linked_hash_table_get_element_count(&table));

    int *value = NULL;
    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(first, *value);

    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, second_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(second, *value);

    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, third_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(third, *value);

    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, fourth_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_INT_EQUALS(fourth, *value);

    const struct aws_linked_list *list = aws_linked_hash_table_get_iteration_list(&table);
    ASSERT_NOT_NULL(list);

    struct aws_linked_list_node *node = aws_linked_list_front(list);

    struct aws_linked_hash_table_node *table_node = AWS_CONTAINER_OF(node, struct aws_linked_hash_table_node, node);
    ASSERT_INT_EQUALS(first, *(int *)table_node->value);

    node = aws_linked_list_next(node);
    ASSERT_NOT_NULL(node);
    table_node = AWS_CONTAINER_OF(node, struct aws_linked_hash_table_node, node);
    ASSERT_INT_EQUALS(second, *(int *)table_node->value);

    node = aws_linked_list_next(node);
    ASSERT_NOT_NULL(node);
    table_node = AWS_CONTAINER_OF(node, struct aws_linked_hash_table_node, node);
    ASSERT_INT_EQUALS(third, *(int *)table_node->value);

    node = aws_linked_list_next(node);
    ASSERT_NOT_NULL(node);
    table_node = AWS_CONTAINER_OF(node, struct aws_linked_hash_table_node, node);
    ASSERT_INT_EQUALS(fourth, *(int *)table_node->value);

    node = aws_linked_list_next(node);
    ASSERT_PTR_EQUALS(aws_linked_list_end(list), node);

    aws_linked_hash_table_clean_up(&table);
    return 0;
}

AWS_TEST_CASE(test_linked_hash_table_preserves_insertion_order, s_test_linked_hash_table_preserves_insertion_order_fn)

struct linked_hash_table_test_value_element {
    bool value_removed;
};

static void s_linked_hash_table_element_value_destroy(void *value) {
    struct linked_hash_table_test_value_element *value_element = value;
    value_element->value_removed = true;
}

static int s_test_linked_hash_table_entries_cleanup_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_linked_hash_table table;

    ASSERT_SUCCESS(aws_linked_hash_table_init(
        &table,
        allocator,
        aws_hash_c_string,
        aws_hash_callback_c_str_eq,
        NULL,
        s_linked_hash_table_element_value_destroy,
        2));

    const char *first_key = "first";
    const char *second_key = "second";

    struct linked_hash_table_test_value_element first = {.value_removed = false};
    struct linked_hash_table_test_value_element second = {.value_removed = false};

    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key, &first));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, second_key, &second));
    ASSERT_INT_EQUALS(2, aws_linked_hash_table_get_element_count(&table));

    ASSERT_SUCCESS(aws_linked_hash_table_remove(&table, second_key));

    ASSERT_TRUE(second.value_removed);
    ASSERT_INT_EQUALS(1, aws_linked_hash_table_get_element_count(&table));

    aws_linked_hash_table_clear(&table);
    ASSERT_INT_EQUALS(0, aws_linked_hash_table_get_element_count(&table));

    ASSERT_TRUE(first.value_removed);
    ASSERT_TRUE(aws_linked_list_empty(aws_linked_hash_table_get_iteration_list(&table)));

    aws_linked_hash_table_clean_up(&table);
    return 0;
}

AWS_TEST_CASE(test_linked_hash_table_entries_cleanup, s_test_linked_hash_table_entries_cleanup_fn)

static int s_test_linked_hash_table_entries_overwrite_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_linked_hash_table table;

    ASSERT_SUCCESS(aws_linked_hash_table_init(
        &table,
        allocator,
        aws_hash_c_string,
        aws_hash_callback_c_str_eq,
        NULL,
        s_linked_hash_table_element_value_destroy,
        2));

    const char *first_key = "first";

    struct linked_hash_table_test_value_element first = {.value_removed = false};
    struct linked_hash_table_test_value_element second = {.value_removed = false};

    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key, &first));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key, &second));
    ASSERT_INT_EQUALS(1, aws_linked_hash_table_get_element_count(&table));

    ASSERT_TRUE(first.value_removed);
    ASSERT_FALSE(second.value_removed);

    struct linked_hash_table_test_value_element *value = NULL;
    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, first_key, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_PTR_EQUALS(&second, value);

    aws_linked_hash_table_clean_up(&table);
    return 0;
}

AWS_TEST_CASE(test_linked_hash_table_entries_overwrite, s_test_linked_hash_table_entries_overwrite_fn)

static int s_test_linked_hash_table_entries_overwrite_reference_unequal_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_linked_hash_table table;

    ASSERT_SUCCESS(aws_linked_hash_table_init(
        &table,
        allocator,
        aws_hash_string,
        aws_hash_callback_string_eq,
        aws_hash_callback_string_destroy,
        s_linked_hash_table_element_value_destroy,
        2));

    struct aws_string *first_key = aws_string_new_from_c_str(allocator, "first");
    struct aws_string *first_key_v2 = aws_string_new_from_c_str(allocator, "first");

    struct linked_hash_table_test_value_element first = {.value_removed = false};
    struct linked_hash_table_test_value_element second = {.value_removed = false};

    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key, &first));
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, first_key_v2, &second));
    ASSERT_INT_EQUALS(1, aws_linked_hash_table_get_element_count(&table));

    ASSERT_TRUE(first.value_removed);
    ASSERT_FALSE(second.value_removed);

    struct linked_hash_table_test_value_element *value = NULL;
    struct aws_string *first_key_v3 = aws_string_new_from_c_str(allocator, "first");
    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, first_key_v3, (void **)&value));
    ASSERT_NOT_NULL(value);
    ASSERT_PTR_EQUALS(&second, value);

    aws_linked_hash_table_clean_up(&table);

    aws_string_destroy(first_key_v3);

    return 0;
}

AWS_TEST_CASE(
    test_linked_hash_table_entries_overwrite_reference_unequal,
    s_test_linked_hash_table_entries_overwrite_reference_unequal_fn)

struct backed_cursor_element {
    struct aws_byte_cursor name_cursor;
    struct aws_byte_buf name;
    uint32_t value;
    struct aws_allocator *allocator;
};

static void s_backed_cursor_element_value_destroy(void *value) {
    struct backed_cursor_element *element = value;

    if (element == NULL) {
        return;
    }

    aws_byte_buf_clean_up(&element->name);

    aws_mem_release(element->allocator, element);
}

static struct backed_cursor_element *s_backed_cursor_element_new(
    struct aws_allocator *allocator,
    struct aws_byte_cursor name,
    uint32_t value) {
    struct backed_cursor_element *element = aws_mem_calloc(allocator, 1, sizeof(struct backed_cursor_element));

    element->allocator = allocator;
    element->value = value;

    if (aws_byte_buf_init_copy_from_cursor(&element->name, allocator, name)) {
        goto on_error;
    }

    element->name_cursor = aws_byte_cursor_from_buf(&element->name);

    return element;

on_error:

    s_backed_cursor_element_value_destroy(element);

    return NULL;
}

static bool s_cursor_hash_equality_fn(const void *a, const void *b) {
    const struct aws_byte_cursor *a_cursor = a;
    const struct aws_byte_cursor *b_cursor = b;

    return aws_byte_cursor_eq(a_cursor, b_cursor);
}

static int s_test_linked_hash_table_entries_overwrite_backed_cursor_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_linked_hash_table table;

    ASSERT_SUCCESS(aws_linked_hash_table_init(
        &table,
        allocator,
        aws_hash_byte_cursor_ptr,
        s_cursor_hash_equality_fn,
        NULL,
        s_backed_cursor_element_value_destroy,
        2));

    struct aws_byte_cursor shared_name = aws_byte_cursor_from_c_str("Hello");
    struct backed_cursor_element *element1 = s_backed_cursor_element_new(allocator, shared_name, 1);
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, &element1->name_cursor, element1));

    struct backed_cursor_element *element1_prime = s_backed_cursor_element_new(allocator, shared_name, 2);
    ASSERT_SUCCESS(aws_linked_hash_table_put(&table, &element1_prime->name_cursor, element1_prime));

    ASSERT_INT_EQUALS(1, aws_linked_hash_table_get_element_count(&table));

    void *element = NULL;
    ASSERT_SUCCESS(aws_linked_hash_table_find(&table, &shared_name, (void **)&element));

    ASSERT_NOT_NULL(element);
    struct backed_cursor_element *found_element = element;
    ASSERT_INT_EQUALS(2, found_element->value);

    aws_linked_hash_table_clean_up(&table);

    return 0;
}

AWS_TEST_CASE(
    test_linked_hash_table_entries_overwrite_backed_cursor,
    s_test_linked_hash_table_entries_overwrite_backed_cursor_fn)
