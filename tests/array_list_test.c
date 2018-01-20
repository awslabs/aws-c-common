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

#include <aws/common/array_list.h>
#include <aws_test_harness.h>

aws_typed_array_list_declaration(int, int)
aws_typed_array_list_definition(int, int)

static int array_list_order_push_back_pop_front_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 4;
    int first = 1, second = 2, third = 3, fourth = 4;

    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List setup should have been successful. err code %d", aws_last_error());
    ASSERT_INT_EQUALS(0, list.length, "List size should be 0.");
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &third), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &fourth), "List push failed with error code %d", aws_last_error());

    ASSERT_INT_EQUALS(list_size, list.length, "List size should be %d.", (int)list_size);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    int item;
    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_INT_EQUALS(list_size - 1, list.length, "List size should be %d.", (int)list_size - 1);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");
    ASSERT_INT_EQUALS(list_size - 2, list.length, "List size should be %d.", (int)list_size - 2);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(third, item, "Item should have been the third item.");
    ASSERT_INT_EQUALS(list_size - 3, list.length, "List size should be %d.", (int)list_size - 3);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(fourth, item, "Item should have been the fourth item.");
    ASSERT_INT_EQUALS(list_size - 4, list.length, "List size should be %d.", (int)list_size - 4);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    aws_int_array_list_clean_up(&list);

    return 0;
}

AWS_TEST_CASE(array_list_order_push_back_pop_front_test, array_list_order_push_back_pop_front_fn)

static int array_list_order_push_back_pop_back_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2, third = 3, fourth = 4;

    ASSERT_INT_EQUALS(0, list.length, "List size should be 0.");
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &third), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &fourth), "List push failed with error code %d", aws_last_error());

    ASSERT_INT_EQUALS(list_size, list.length, "List size should be %d.", (int)list_size);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    int item;
    ASSERT_SUCCESS(aws_int_array_list_back(&list, &item), "List back failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_back(&list), "List pop back failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(fourth, item, "Item should have been the fourth item.");
    ASSERT_INT_EQUALS(list_size - 1, list.length, "List size should be %d.", (int)list_size - 4);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_back(&list, &item), "List back failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_back(&list), "List pop back failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(third, item, "Item should have been the third item.");
    ASSERT_INT_EQUALS(list_size - 2, list.length, "List size should be %d.", (int)list_size - 3);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_back(&list, &item), "List back failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_back(&list), "List pop back failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");
    ASSERT_INT_EQUALS(list_size - 3, list.length, "List size should be %d.", (int)list_size - 2);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_back(&list, &item), "List back failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_back(&list), "List pop back failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_INT_EQUALS(list_size - 4, list.length, "List size should be %d.", (int)list_size - 1);
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);


    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_order_push_back_pop_back_test, array_list_order_push_back_pop_back_fn)

static int array_list_exponential_mem_model_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 1;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2, third = 3;

    ASSERT_INT_EQUALS(0, list.length, "List size should be 0.");
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "array list push back failed with error %d", aws_last_error());
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "array list push back failed with error %d", aws_last_error());
    ASSERT_INT_EQUALS(list_size << 1, list.current_size, "Allocated list size should be %d.", (int)list_size << 1);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &third), "array list push back failed with error %d", aws_last_error());
    ASSERT_INT_EQUALS(list_size << 2, list.current_size, "Allocated list size should be %d.", (int)list_size << 2);

    ASSERT_INT_EQUALS(3, list.length, "List size should be %d.", 3);

    int item;
    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");

    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");

    ASSERT_SUCCESS(aws_int_array_list_front(&list, &item), "List front failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_pop_front(&list), "List pop front failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(third, item, "Item should have been the third item.");

    ASSERT_INT_EQUALS(0, list.length, "List size should be 0.");
    ASSERT_INT_EQUALS(list_size << 2, list.current_size, "Allocated list size should be %d.", (int)list_size << 2);

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_exponential_mem_model_test, array_list_exponential_mem_model_test_fn)

static int array_list_iteration_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2, third = 3, fourth = 4;

    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &first, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &second, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &third, 2), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(3, list.length, "List size should be %d.", 3);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &fourth, 3), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(4, list.length, "List size should be %d.", 4);

    int item;
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 2), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(third, item, "Item should have been the third item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 3), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(fourth, item, "Item should have been the fourth item.");

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_iteration_test, array_list_iteration_test_fn)

static int array_list_preallocated_iteration_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static const size_t list_size = 4;
    static int list_data[4];
    ASSERT_SUCCESS(aws_int_array_list_init_static(&list, list_data, list_size), "Static list init failed with error code %d", aws_last_error());

    int first = 1, second = 2, third = 3, fourth = 4;

    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &first, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &second, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &third, 2), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(3, list.length, "List size should be %d.", 3);
    ASSERT_SUCCESS(aws_int_array_list_set_at(&list, &fourth, 3), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(4, list.length, "List size should be %d.", 4);
    ASSERT_FAILS(aws_int_array_list_set_at(&list, &fourth, 4), "Adding element past the end should have failed");
    ASSERT_INT_EQUALS(AWS_ERROR_INVALID_INDEX, aws_last_error(), "Error code should have been INVALID_INDEX but was %d", aws_last_error());

    int item;
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 2), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(third, item, "Item should have been the third item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 3), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(fourth, item, "Item should have been the fourth item.");
    ASSERT_FAILS(aws_int_array_list_get_at(&list, &item, 4), "Getting an element past the end should have failed");
    ASSERT_INT_EQUALS(AWS_ERROR_INVALID_INDEX, aws_last_error(), "Error code should have been INVALID_INDEX but was %d", aws_last_error());

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_preallocated_iteration_test, array_list_preallocated_iteration_test_fn)

static int array_list_preallocated_push_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static const size_t list_size = 4;
    static int list_data[4];
    ASSERT_SUCCESS(aws_int_array_list_init_static(&list, list_data, list_size), "Static list init failed with error code %d", aws_last_error());

    int first = 1, second = 2, third = 3, fourth = 4;

    ASSERT_INT_EQUALS(0, list.length, "List size should be 0.");
    ASSERT_INT_EQUALS(list_size, list.current_size, "Allocated list size should be %d.", (int)list_size);

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &third), "List push failed with error code %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &fourth), "List push failed with error code %d", aws_last_error());
    ASSERT_FAILS(aws_int_array_list_push_back(&list, &fourth), "List push past static size should have failed");
    ASSERT_INT_EQUALS(AWS_ERROR_LIST_EXCEEDS_MAX_SIZE, aws_last_error(), "Error code should have been LIST_EXCEEDS_MAX_SIZE but was %d", aws_last_error());

    aws_int_array_list_clean_up(&list);

    return 0;
}

AWS_TEST_CASE(array_list_preallocated_push_test, array_list_preallocated_push_test_fn)


static int array_list_shrink_to_fit_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2;

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);

    ASSERT_INT_EQUALS(list_size, list.current_size, "size before shrink should be %d.", list_size);

    ASSERT_SUCCESS(aws_int_array_list_shrink_to_fit(&list), "List shrink to fit failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);
    ASSERT_INT_EQUALS(2, list.current_size, "Shrunken size should be %d.", 2);

    int item;
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list, &item, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");
    ASSERT_FAILS(aws_int_array_list_get_at(&list, &item, 2), "Getting an element past the end should have failed");
    ASSERT_INT_EQUALS(AWS_ERROR_INVALID_INDEX, aws_last_error(), "Error code should have been INVALID_INDEX but was %d", aws_last_error());

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_shrink_to_fit_test, array_list_shrink_to_fit_test_fn)

static int array_list_shrink_to_fit_static_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static const size_t list_size = 4;
    static int list_data[4];
    ASSERT_SUCCESS(aws_int_array_list_init_static(&list, list_data, list_size), "Static list init failed with error code %d", aws_last_error());

    int first = 1, second = 2;

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);

    ASSERT_INT_EQUALS(list_size, list.current_size, "size before shrink should be %d.", list_size);

    ASSERT_FAILS(aws_int_array_list_shrink_to_fit(&list), "List shrink of static list should have failed.");
    ASSERT_INT_EQUALS(AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK, aws_last_error(), "Error code should have been LIST_STATIC_MODE_CANT_SHRINK but was %d", aws_last_error());

    ASSERT_INT_EQUALS(&list_data, list.data, "The underlying allocation should not have changed");
    ASSERT_INT_EQUALS(list_size, list.current_size, "List size should not have been changed");

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_shrink_to_fit_static_test, array_list_shrink_to_fit_static_test_fn)

static int array_list_clear_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2;

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list.length, "List size should be %d.", 2);

    ASSERT_INT_EQUALS(list_size, list.current_size, "size before clear should be %d.", list_size);

    aws_int_array_list_clear(&list);
    ASSERT_INT_EQUALS(0, list.length, "List size should be %d after clear.", 0);
    ASSERT_INT_EQUALS(list_size, list.current_size, "cleared size should be %d.", (int)list_size);

    int item;
    ASSERT_FAILS(aws_int_array_list_front(&list, &item), "front() after a clear on list should have been an error");
    ASSERT_INT_EQUALS(AWS_ERROR_LIST_EMPTY, aws_last_error(), "Error code should have been LIST_EMPTY but was %d", aws_last_error());

    aws_int_array_list_clean_up(&list);
    return 0;
}

AWS_TEST_CASE(array_list_clear_test, array_list_clear_test_fn)

static int array_list_copy_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list_a;
    struct aws_int_array_list list_b;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list_a, alloc, list_size), "List initialization failed with error %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list_b, alloc, list_size), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2;

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list_a, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list_a.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list_a, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list_a.length, "List size should be %d.", 2);

    ASSERT_SUCCESS(aws_int_array_list_copy(&list_a, &list_b), "List copy failed with error code %d", aws_last_error());

    int item;
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list_b, &item, 0), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(first, item, "Item should have been the first item.");
    ASSERT_SUCCESS(aws_int_array_list_get_at(&list_b, &item, 1), "Array set failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(second, item, "Item should have been the second item.");

    ASSERT_INT_EQUALS(aws_int_array_list_length(&list_a), aws_int_array_list_length(&list_b), "list lengths should have matched.");

    aws_int_array_list_clean_up(&list_a);
    aws_int_array_list_clean_up(&list_b);
    return 0;
}

AWS_TEST_CASE(array_list_copy_test, array_list_copy_test_fn)

static int array_list_not_enough_space_test_fn(struct aws_allocator *alloc, void *ctx) {
    struct aws_int_array_list list_a;
    struct aws_int_array_list list_b;

    static size_t list_size = 4;
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list_a, alloc, list_size), "List initialization failed with error %d", aws_last_error());
    ASSERT_SUCCESS(aws_int_array_list_init_dynamic(&list_b, alloc, 1), "List initialization failed with error %d", aws_last_error());

    int first = 1, second = 2;

    ASSERT_SUCCESS(aws_int_array_list_push_back(&list_a, &first), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(1, list_a.length, "List size should be %d.", 1);
    ASSERT_SUCCESS(aws_int_array_list_push_back(&list_a, &second), "List push failed with error code %d", aws_last_error());
    ASSERT_INT_EQUALS(2, list_a.length, "List size should be %d.", 2);

    ASSERT_FAILS(aws_int_array_list_copy(&list_a, &list_b), "Copy from list_a to list_b should have failed");
    ASSERT_INT_EQUALS(AWS_ERROR_LIST_DEST_COPY_TOO_SMALL, aws_last_error(), "List copy should have failed since list_b doesn't have enough space.");

    aws_int_array_list_clean_up(&list_a);
    aws_int_array_list_clean_up(&list_b);

    return 0;
}

AWS_TEST_CASE(array_list_not_enough_space_test, array_list_not_enough_space_test_fn)
