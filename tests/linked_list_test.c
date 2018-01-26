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

#include <aws/common/linked_list.h>
#include <aws_test_harness.h>

aws_linked_list_of(int, int_value);

static int test_linked_list_order_push_back_pop_front() {
    struct aws_linked_list_node list, *head;

    head = &list;
    aws_linked_list_init(head);

    struct int_value first = (struct int_value){.value = 1};
    struct int_value second = (struct int_value){.value = 2};
    struct int_value third = (struct int_value){.value = 3};
    struct int_value fourth = (struct int_value){.value = 4};

    aws_linked_list_push_back(head, &first.list);
    aws_linked_list_push_back(head, &second.list);
    aws_linked_list_push_back(head, &third.list);
    aws_linked_list_push_back(head, &fourth.list);

    int item;
    aws_linked_list_pop_front(head);
    item = aws_container_of(head, struct int_value, list)->value;
    ASSERT_INT_EQUALS(first.value, item, "Item should have been the first item.");

    aws_linked_list_pop_front(head);
    item = aws_container_of(head, struct int_value, list)->value;
    ASSERT_INT_EQUALS(second.value, item, "Item should have been the second item.");

    aws_linked_list_pop_front(head);
    item = aws_container_of(head, struct int_value, list)->value;
    ASSERT_INT_EQUALS(third.value, item, "Item should have been the third item.");

    aws_linked_list_pop_front(head);
    item = aws_container_of(head, struct int_value, list)->value;
    ASSERT_INT_EQUALS(fourth.value, item, "Item should have been the fourth item.");

    return 0;
}

static int test_linked_list_order_push_front_pop_back() {
    struct aws_linked_list_node list, *head;

    head = &list;
    aws_linked_list_init(head);

    ASSERT_TRUE(aws_linked_list_empty(head), "List should be empty before adding any items.");

    struct int_value first = (struct int_value){.value = 1};
    struct int_value second = (struct int_value){.value = 2};
    struct int_value third = (struct int_value){.value = 3};
    struct int_value fourth = (struct int_value){.value = 4};

    aws_linked_list_push_front(head, &first.list);
    aws_linked_list_push_front(head, &second.list);
    aws_linked_list_push_front(head, &third.list);
    aws_linked_list_push_front(head, &fourth.list);

    ASSERT_FALSE(aws_linked_list_empty(head), "List should not be empty after adding items.");

    int item;
    aws_linked_list_pop_back(head);
    item = aws_container_of(head->prev, struct int_value, list)->value;
    ASSERT_INT_EQUALS(second.value, item, "Item should have been the second item.");

    aws_linked_list_pop_back(head);
    item = aws_container_of(head->prev, struct int_value, list)->value;
    ASSERT_INT_EQUALS(third.value, item, "Item should have been the third item.");

    aws_linked_list_pop_back(head);
    item = aws_container_of(head->prev, struct int_value, list)->value;
    ASSERT_INT_EQUALS(fourth.value, item, "Item should have been the fourth item.");

    aws_linked_list_pop_back(head);
    ASSERT_TRUE(aws_linked_list_empty(head), "List should be after removing all items.");

    return 0;
}

AWS_TEST_CASE(linked_list_push_back_pop_front, test_linked_list_order_push_back_pop_front)
AWS_TEST_CASE(linked_list_push_front_pop_back, test_linked_list_order_push_front_pop_back)
