/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/byte_buf.h>
#include <aws/common/string.h>

#include <aws/common/json.h>

static char *s_test_json = "{\"array\":[1,2,3],\"boolean\":true,\"color\":\"gold\",\"null\":null,\"number\":123,"
                           "\"object\":{\"a\":\"b\",\"c\":\"d\"}}";

AWS_TEST_CASE(test_json_parse_from_string, s_test_json_parse_from_string)
static int s_test_json_parse_from_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);
    struct aws_json_value *root = aws_json_value_new_from_string(allocator, aws_byte_cursor_from_c_str(s_test_json));

    ASSERT_NOT_NULL(root);
    ASSERT_TRUE(aws_json_value_is_object(root));

    // Testing valid array
    struct aws_json_value *array_node = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("array"));
    ASSERT_NOT_NULL(array_node);
    ASSERT_TRUE(aws_json_value_is_array(array_node));
    ASSERT_TRUE(aws_json_get_array_size(array_node) == 3);
    struct aws_json_value *array_node_one = aws_json_get_array_element(array_node, 0);
    ASSERT_NOT_NULL(array_node_one);
    ASSERT_TRUE(aws_json_value_is_number(array_node_one));
    double double_check_value = 0;
    ASSERT_INT_EQUALS(AWS_OP_SUCCESS, aws_json_value_get_number(array_node_one, &double_check_value));
    ASSERT_NOT_NULL(double_check_value);
    ASSERT_TRUE(double_check_value == (double)1);

    // Testing valid boolean
    struct aws_json_value *boolean_node = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("boolean"));
    ASSERT_NOT_NULL(boolean_node);
    ASSERT_TRUE(aws_json_value_is_boolean(boolean_node));
    bool bool_check_value = false;
    aws_json_value_get_boolean(boolean_node, &bool_check_value);
    ASSERT_TRUE(bool_check_value);

    // Testing valid string
    struct aws_json_value *string_node = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("color"));
    ASSERT_NOT_NULL(string_node);
    ASSERT_TRUE(aws_json_value_is_string(string_node));
    struct aws_byte_cursor str_string_check_value;
    aws_json_value_get_string(string_node, &str_string_check_value);
    struct aws_string *tmp_str = aws_string_new_from_cursor(allocator, &str_string_check_value);
    ASSERT_TRUE(strcmp(aws_string_c_str(tmp_str), "gold") == 0);
    aws_string_destroy_secure(tmp_str);

    // Testing valid number
    struct aws_json_value *number_node = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("number"));
    ASSERT_NOT_NULL(number_node);
    ASSERT_TRUE(aws_json_value_is_number(number_node));
    double double_test_two = 0;
    aws_json_value_get_number(number_node, &double_test_two);
    ASSERT_TRUE(double_test_two == (double)123);

    // Testing valid object
    struct aws_json_value *object_node = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("object"));
    ASSERT_NOT_NULL(object_node);
    ASSERT_TRUE(aws_json_value_is_object(object_node));
    struct aws_json_value *sub_object_node =
        aws_json_value_get_from_object(object_node, aws_byte_cursor_from_c_str("a"));
    ASSERT_NOT_NULL(sub_object_node);
    ASSERT_TRUE(aws_json_value_is_string(sub_object_node));
    struct aws_byte_cursor str_a_value_cursor;
    aws_json_value_get_string(sub_object_node, &str_a_value_cursor);
    struct aws_string *sub_a_string = aws_string_new_from_cursor(allocator, &str_a_value_cursor);
    ASSERT_TRUE(strcmp(aws_string_c_str(sub_a_string), "b") == 0);
    aws_string_destroy_secure(sub_a_string);

    // Testing invalid object
    struct aws_json_value *invalid_object = aws_json_value_get_from_object(root, aws_byte_cursor_from_c_str("invalid"));
    ASSERT_NULL(invalid_object);
    ASSERT_INT_EQUALS(aws_json_value_get_number(invalid_object, NULL), AWS_OP_ERR);
    // Test getting invalid type of data
    ASSERT_INT_EQUALS(aws_json_value_get_number(string_node, NULL), AWS_OP_ERR);

    aws_json_value_destroy(root);
    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_json_parse_to_string, s_test_json_parse_to_string)
static int s_test_json_parse_to_string(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_common_library_init(allocator);
    struct aws_json_value *root = aws_json_value_new_object(allocator);

    struct aws_json_value *array = aws_json_value_new_array(allocator);
    aws_json_value_add_array_element(array, aws_json_value_new_number(allocator, 1));
    aws_json_value_add_array_element(array, aws_json_value_new_number(allocator, 2));
    aws_json_value_add_array_element(array, aws_json_value_new_number(allocator, 3));
    aws_json_value_add_to_object(root, aws_byte_cursor_from_c_str("array"), array);

    aws_json_value_add_to_object(
        root, aws_byte_cursor_from_c_str("boolean"), aws_json_value_new_boolean(allocator, true));
    aws_json_value_add_to_object(
        root,
        aws_byte_cursor_from_c_str("color"),
        aws_json_value_new_string(allocator, aws_byte_cursor_from_c_str("gold")));
    aws_json_value_add_to_object(root, aws_byte_cursor_from_c_str("null"), aws_json_value_new_null(allocator));
    aws_json_value_add_to_object(root, aws_byte_cursor_from_c_str("number"), aws_json_value_new_number(allocator, 123));

    struct aws_json_value *object = aws_json_value_new_object(allocator);
    aws_json_value_add_to_object(
        object, aws_byte_cursor_from_c_str("a"), aws_json_value_new_string(allocator, aws_byte_cursor_from_c_str("b")));
    aws_json_value_add_to_object(
        object, aws_byte_cursor_from_c_str("c"), aws_json_value_new_string(allocator, aws_byte_cursor_from_c_str("d")));
    aws_json_value_add_to_object(root, aws_byte_cursor_from_c_str("object"), object);

    struct aws_byte_buf result_string_buf;
    aws_byte_buf_init(&result_string_buf, allocator, 0);

    ASSERT_INT_EQUALS(AWS_OP_SUCCESS, aws_byte_buf_append_json_string(root, &result_string_buf));
    struct aws_string *result_string = aws_string_new_from_buf(allocator, &result_string_buf);
    ASSERT_STR_EQUALS(s_test_json, aws_string_c_str(result_string));
    aws_byte_buf_clean_up_secure(&result_string_buf);
    aws_string_destroy_secure(result_string);

    aws_json_value_destroy(root);
    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}
