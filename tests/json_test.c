/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/

#include <aws/testing/aws_test_harness.h>
#include <aws/common/json/json.h>

//static char* s_test_json = "{array: [1,2,3], boolean: true, color: gold, null: null, number: 123, object: {a: b, c: d}}";
//static char* s_test_json = "{\"array\": [1,2,3]}";

static char* s_test_json = "{\"array\": [1,2,3], \"boolean\": true, \"color\": \"gold\", \"null\": null, \"number\": 123, \"object\": {\"a\": \"b\", \"c\": \"d\"}}";
// =========



AWS_TEST_CASE(test_json_parse_from_string, s_test_json_parse_from_string)
static int s_test_json_parse_from_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_json_module_init(allocator);
    void *root = aws_json_node_from_string(s_test_json);

    //fprintf(stdout, "%s", aws_json_node_to_string_formatted(root));

    ASSERT_NOT_NULL(root);
    AWS_ASSERT(aws_json_node_is_object(root));

    // Testing valid array
    void* array_node = aws_json_object_get_node(root, "array");
    ASSERT_NOT_NULL(array_node);
    ASSERT_TRUE(aws_json_node_is_array(array_node));
    ASSERT_TRUE(aws_json_array_get_count(array_node) == 3);
    void* array_node_one = aws_json_array_get_node(array_node, 0);
    ASSERT_NOT_NULL(array_node_one);
    ASSERT_TRUE(aws_json_node_is_number(array_node_one));
    ASSERT_TRUE(*aws_json_node_get_number(array_node_one) == (double)1);

    // Testing valid boolean
    void* boolean_node = aws_json_object_get_node(root, "boolean");
    ASSERT_NOT_NULL(boolean_node);
    ASSERT_TRUE(aws_json_node_is_boolean(boolean_node));
    ASSERT_TRUE(aws_json_node_get_boolean(boolean_node));

    // Testing valid string
    void* string_node = aws_json_object_get_node(root, "color");
    ASSERT_NOT_NULL(string_node);
    ASSERT_TRUE(aws_json_node_is_string(string_node));
    ASSERT_TRUE(strcmp(aws_json_node_get_string(string_node), "gold") == 0);

    // Testing valid number
    void *number_node = aws_json_object_get_node(root, "number");
    ASSERT_NOT_NULL(number_node);
    ASSERT_TRUE(aws_json_node_is_number(number_node));
    ASSERT_TRUE(*aws_json_node_get_number(number_node) == (double)123);

    // Testing valid object
    void *object_node = aws_json_object_get_node(root, "object");
    ASSERT_NOT_NULL(object_node);
    ASSERT_TRUE(aws_json_node_is_object(object_node) == true);
    void *sub_object_node = aws_json_object_get_node(object_node, "a");
    ASSERT_NOT_NULL(sub_object_node);
    ASSERT_TRUE(aws_json_node_is_string(sub_object_node));
    ASSERT_TRUE(strcmp(aws_json_node_get_string(sub_object_node), "b") == 0);

    aws_json_node_delete(root);
    aws_json_module_cleanup();

    return 0;
}
