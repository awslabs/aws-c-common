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
#include <aws/testing/aws_test_harness.h>

struct int_value {
    int value;
    struct aws_linked_list_node node;
};

static int test_linked_list_order_push_back_pop_front(struct aws_allocator *allocator, void *ctx) {
    struct aws_linked_list list;

    aws_linked_list_init(&list);
    ASSERT_TRUE(aws_linked_list_empty(&list));

    struct int_value first = (struct int_value){.value = 1};
    struct int_value second = (struct int_value){.value = 2};
    struct int_value third = (struct int_value){.value = 3};
    struct int_value fourth = (struct int_value){.value = 4};

    aws_linked_list_push_back(&list, &first.node);
    aws_linked_list_push_back(&list, &second.node);
    aws_linked_list_push_back(&list, &third.node);
    aws_linked_list_push_back(&list, &fourth.node);

    int item;
    struct aws_linked_list_node *node = aws_linked_list_pop_front(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(first.value, item);

    node = aws_linked_list_pop_front(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(second.value, item);

    node = aws_linked_list_pop_front(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(third.value, item);

    node = aws_linked_list_pop_front(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(fourth.value, item);

    ASSERT_TRUE(aws_linked_list_empty(&list));
    return 0;
}

static int test_linked_list_order_push_front_pop_back(struct aws_allocator *allocator, void *ctx) {
    struct aws_linked_list list;

    aws_linked_list_init(&list);

    ASSERT_TRUE(aws_linked_list_empty(&list));

    struct int_value first = (struct int_value){.value = 1};
    struct int_value second = (struct int_value){.value = 2};
    struct int_value third = (struct int_value){.value = 3};
    struct int_value fourth = (struct int_value){.value = 4};

    aws_linked_list_push_front(&list, &first.node);
    aws_linked_list_push_front(&list, &second.node);
    aws_linked_list_push_front(&list, &third.node);
    aws_linked_list_push_front(&list, &fourth.node);

    ASSERT_FALSE(aws_linked_list_empty(&list));

    int item;
    struct aws_linked_list_node *node = aws_linked_list_pop_back(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(first.value, item);

    node = aws_linked_list_pop_back(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(second.value, item);

    node = aws_linked_list_pop_back(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(third.value, item);

    node = aws_linked_list_pop_back(&list);
    item = aws_container_of(node, struct int_value, node)->value;
    ASSERT_INT_EQUALS(fourth.value, item);

    ASSERT_TRUE(aws_linked_list_empty(&list));

    return 0;
}

AWS_TEST_CASE(linked_list_push_back_pop_front, test_linked_list_order_push_back_pop_front)
AWS_TEST_CASE(linked_list_push_front_pop_back, test_linked_list_order_push_front_pop_back)
