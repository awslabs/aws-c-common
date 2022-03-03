/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/

#include <aws/testing/aws_test_harness.h>
#include <aws/common/json/json_data.h>
#include <aws/common/json/json_converter.h

static char* s_test_json = "{\"array\": [1,2,3], \"boolean\": true, \"color\": \"gold\", \"null\": null, \"number\": 123, \"object\": {\"a\": \"b\", \"c\": \"d\"}}";
// =========



AWS_TEST_CASE(test_json_parse_from_string, s_test_json_parse_from_string)
static int s_test_json_parse_from_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_json_converter_init(allocator);
    struct aws_json_node *root = aws_parse_json_from_string(s_test_json);
    AWS_ASSERT(root != NULL);
    AWS_ASSERT(aws_json_node_is_object(root) == true);

    // Testing valid array
    struct aws_json_node *array_node = aws_json_get_node_from_object(root, "array");
    AWS_ASSERT(array_node != NULL);
    AWS_ASSERT(aws_json_node_is_array(array_node) == true);
    struct aws_json_node *array_node_one = aws_json_get_node_from_array(array_node, 0);
    AWS_ASSERT(array_node_one != NULL);
    AWS_ASSERT(aws_json_node_is_number(array_node_one) == true);
    AWS_ASSERT(*aws_json_node_get_number(array_node_one) == 1);

    // Testing valid boolean
    struct aws_json_node *boolean_node = aws_json_get_node_from_object(root, "boolean");
    AWS_ASSERT(boolean_node != NULL);
    AWS_ASSERT(aws_json_node_is_boolean(boolean_node) == true);
    AWS_ASSERT(*aws_json_node_get_boolean(boolean_node) == true);

    // Testing valid string
    struct aws_json_node *string_node = aws_json_get_node_from_object(root, "color");
    AWS_ASSERT(string_node != NULL);
    AWS_ASSERT(aws_json_node_is_string(string_node) == true);
    AWS_ASSERT(strcmp(aws_json_node_get_string(string_node), "gold") == 0);

    // Testing valid number
    struct aws_json_node *number_node = aws_json_get_node_from_object(root, "number");
    AWS_ASSERT(string_node != NULL);
    AWS_ASSERT(aws_json_node_is_number(number_node) == true);
    AWS_ASSERT(*aws_json_node_get_number(number_node) == 123);

    // Testing valid object
    struct aws_json_node *object_node = aws_json_get_node_from_object(root, "object");
    AWS_ASSERT(object_node != NULL);
    AWS_ASSERT(aws_json_node_is_object(object_node) == true);
    struct aws_json_node *sub_object_node = aws_json_get_node_from_object(object_node, "a");
    AWS_ASSERT(sub_object_node != NULL);
    AWS_ASSERT(aws_json_node_is_string(sub_object_node));
    AWS_ASSERT(strcmp(aws_json_node_get_string(sub_object_node), "b") == 0);

    aws_json_node_delete(root);
    aws_json_converter_clean_up();

    return 0;
}
