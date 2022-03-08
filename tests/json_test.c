/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/

#include <aws/testing/aws_test_harness.h>

#include <aws/common/byte_buf.h>
#include <aws/common/string.h>

#include <aws/common/json.h>

static char* s_test_json = "{\"array\":[1,2,3],\"boolean\":true,\"color\":\"gold\",\"null\":null,\"number\":123,\"object\":{\"a\":\"b\",\"c\":\"d\"}}";

AWS_TEST_CASE(test_json_parse_from_string, s_test_json_parse_from_string)
static int s_test_json_parse_from_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_json_module_init(allocator);
    struct aws_byte_cursor str_s_test_json_cursor = aws_byte_cursor_from_c_str(s_test_json);
    struct aws_json_value *root = aws_json_from_string(&str_s_test_json_cursor, allocator);

    ASSERT_NOT_NULL(root);
    ASSERT_TRUE(aws_json_is_object(root));

    // Testing valid array
    struct aws_byte_cursor str_array_cursor = aws_byte_cursor_from_c_str("array");
    struct aws_json_value* array_node = aws_json_object_get(root, &str_array_cursor, allocator);
    ASSERT_NOT_NULL(array_node);
    ASSERT_TRUE(aws_json_is_array(array_node));
    ASSERT_TRUE(aws_json_array_get_count(array_node) == 3);
    struct aws_json_value* array_node_one = aws_json_array_get(array_node, 0);
    ASSERT_NOT_NULL(array_node_one);
    ASSERT_TRUE(aws_json_is_number(array_node_one));
    double double_check_value = 0;
    ASSERT_INT_EQUALS(AWS_OP_SUCCESS, aws_json_value_get_number(array_node_one, &double_check_value));
    ASSERT_NOT_NULL(double_check_value);
    ASSERT_TRUE(double_check_value == (double)1);

    // Testing valid boolean
    struct aws_byte_cursor str_boolean_cursor = aws_byte_cursor_from_c_str("boolean");
    struct aws_json_value* boolean_node = aws_json_object_get(root, &str_boolean_cursor, allocator);
    ASSERT_NOT_NULL(boolean_node);
    ASSERT_TRUE(aws_json_is_boolean(boolean_node));
    bool bool_check_value = false;
    aws_json_value_get_boolean(boolean_node, &bool_check_value);
    ASSERT_TRUE(bool_check_value);

    // Testing valid string
    struct aws_byte_cursor str_color_cursor = aws_byte_cursor_from_c_str("color");
    struct aws_json_value* string_node = aws_json_object_get(root, &str_color_cursor, allocator);
    ASSERT_NOT_NULL(string_node);
    ASSERT_TRUE(aws_json_is_string(string_node));
    struct aws_byte_cursor str_string_check_value;
    aws_json_value_get_string(string_node, &str_string_check_value);
    struct aws_string *tmp_str = aws_string_new_from_cursor(allocator, &str_string_check_value);
    ASSERT_TRUE(strcmp(aws_string_c_str(tmp_str), "gold") == 0);
    aws_string_destroy_secure(tmp_str);

    // Testing valid number
    struct aws_byte_cursor str_number_cursor = aws_byte_cursor_from_c_str("number");
    struct aws_json_value *number_node = aws_json_object_get(root, &str_number_cursor, allocator);
    ASSERT_NOT_NULL(number_node);
    ASSERT_TRUE(aws_json_is_number(number_node));
    double double_test_two = 0;
    aws_json_value_get_number(number_node, &double_test_two);
    ASSERT_TRUE(double_test_two == (double)123);

    // Testing valid object
    struct aws_byte_cursor str_object_cursor = aws_byte_cursor_from_c_str("object");
    struct aws_json_value *object_node = aws_json_object_get(root, &str_object_cursor, allocator);
    ASSERT_NOT_NULL(object_node);
    ASSERT_TRUE(aws_json_is_object(object_node));
    struct aws_byte_cursor str_a_cursor = aws_byte_cursor_from_c_str("a");
    struct aws_json_value *sub_object_node = aws_json_object_get(object_node, &str_a_cursor, allocator);
    ASSERT_NOT_NULL(sub_object_node);
    ASSERT_TRUE(aws_json_is_string(sub_object_node));
    struct aws_byte_cursor str_a_value_cursor;
    aws_json_value_get_string(sub_object_node, &str_a_value_cursor);
    struct aws_string *sub_a_string = aws_string_new_from_cursor(allocator, &str_a_value_cursor);
    ASSERT_TRUE(strcmp(aws_string_c_str(sub_a_string), "b") == 0);
    aws_string_destroy_secure(sub_a_string);

    // Testing invalid object
    struct aws_byte_cursor str_invalid_cursor = aws_byte_cursor_from_c_str("invalid");
    struct aws_json_value *invalid_object = aws_json_object_get(root, &str_invalid_cursor, allocator);
    ASSERT_NULL(invalid_object);
    ASSERT_INT_EQUALS(aws_json_value_get_number(invalid_object, NULL), AWS_OP_ERR);
    // Test getting invalid type of data
    ASSERT_INT_EQUALS(aws_json_value_get_number(string_node, NULL), AWS_OP_ERR);

    aws_json_destroy(root);
    aws_json_module_cleanup();

    return 0;
}

AWS_TEST_CASE(test_json_parse_to_string, s_test_json_parse_to_string)
static int s_test_json_parse_to_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_json_module_init(allocator);

    struct aws_json_value *root = aws_json_object_new(allocator);

    struct aws_json_value *array = aws_json_array_new(allocator);
    aws_json_array_add(array, aws_json_number_new(1, allocator));
    aws_json_array_add(array, aws_json_number_new(2, allocator));
    aws_json_array_add(array, aws_json_number_new(3, allocator));
    struct aws_byte_cursor str_array_cursor = aws_byte_cursor_from_c_str("array");
    aws_json_object_add(root, &str_array_cursor, allocator, array);

    struct aws_byte_cursor str_boolean_cursor = aws_byte_cursor_from_c_str("boolean");
    aws_json_object_add(root, &str_boolean_cursor, allocator, aws_json_boolean_new(true, allocator));
    struct aws_byte_cursor str_color_cursor = aws_byte_cursor_from_c_str("color");
    struct aws_byte_cursor str_gold_cursor = aws_byte_cursor_from_c_str("gold");
    aws_json_object_add(root, &str_color_cursor, allocator, aws_json_string_new(&str_gold_cursor, allocator));
    struct aws_byte_cursor str_null_cursor = aws_byte_cursor_from_c_str("null");
    aws_json_object_add(root, &str_null_cursor, allocator, aws_json_null_new(allocator));
    struct aws_byte_cursor str_number_cursor = aws_byte_cursor_from_c_str("number");
    aws_json_object_add(root, &str_number_cursor, allocator, aws_json_number_new(123, allocator));

    struct aws_json_value *object = aws_json_object_new(allocator);
    struct aws_byte_cursor str_a_cursor = aws_byte_cursor_from_c_str("a");
    struct aws_byte_cursor str_b_cursor = aws_byte_cursor_from_c_str("b");
    struct aws_byte_cursor str_c_cursor = aws_byte_cursor_from_c_str("c");
    struct aws_byte_cursor str_d_cursor = aws_byte_cursor_from_c_str("d");
    aws_json_object_add(object, &str_a_cursor, allocator, aws_json_string_new(&str_b_cursor, allocator));
    aws_json_object_add(object, &str_c_cursor, allocator, aws_json_string_new(&str_d_cursor, allocator));
    struct aws_byte_cursor str_object_cursor = aws_byte_cursor_from_c_str("object");
    aws_json_object_add(root, &str_object_cursor, allocator, object);

    struct aws_byte_cursor result_string_cursor;
    ASSERT_INT_EQUALS(AWS_OP_SUCCESS, aws_json_to_string(root, &result_string_cursor));
    struct aws_string *result_string = aws_string_new_from_cursor(allocator, &result_string_cursor);
    ASSERT_STR_EQUALS(aws_string_c_str(result_string), s_test_json);
    aws_string_destroy_secure(result_string);

    aws_json_destroy(root);
    aws_json_module_cleanup();

    return 0;
}
