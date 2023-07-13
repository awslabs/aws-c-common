/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/xml_parser.h>
#include <aws/testing/aws_test_harness.h>

const char *root_with_text = "<?xml version=\"1.0\" encoding=\"UTF-8\"?><rootNode>TestBody</rootNode>";

struct root_with_text_capture {
    struct aws_byte_cursor capture;
    struct aws_byte_cursor node_name;
};

int s_root_with_text_root_node(struct aws_xml_node *node, void *user_data) {
    struct root_with_text_capture *capture = user_data;
    if (aws_xml_node_as_body(node, &capture->capture)) {
        return AWS_OP_ERR;
    }
    capture->node_name = aws_xml_node_get_name(node);

    return AWS_OP_SUCCESS;
}

static int s_xml_parser_root_with_text_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct root_with_text_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(root_with_text),
        .on_root_encountered = s_root_with_text_root_node,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "rootNode";
    const char expected_value[] = "TestBody";

    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.node_name.ptr, capture.node_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value, sizeof(expected_value) - 1, capture.capture.ptr, capture.capture.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_root_with_text, s_xml_parser_root_with_text_test)

const char *child_with_text =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?><rootNode><child1>TestBody</child1></rootNode>";

struct child_text_capture {
    struct aws_byte_cursor capture;
    struct aws_byte_cursor node_name;
};

int s_child_with_text_root_node(struct aws_xml_node *node, void *user_data) {
    struct child_text_capture *capture = user_data;
    if (aws_xml_node_as_body(node, &capture->capture)) {
        return AWS_OP_ERR;
    }
    capture->node_name = aws_xml_node_get_name(node);

    return AWS_OP_SUCCESS;
}

int s_root_with_child(struct aws_xml_node *node, void *user_data) {
    if (aws_xml_node_traverse(node, s_child_with_text_root_node, user_data)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

static int s_xml_parser_child_with_text_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct child_text_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(child_with_text),
        .on_root_encountered = s_root_with_child,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child1";
    const char expected_value[] = "TestBody";

    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.node_name.ptr, capture.node_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value, sizeof(expected_value) - 1, capture.capture.ptr, capture.capture.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_child_with_text, s_xml_parser_child_with_text_test)

const char *siblings_with_text =
    "<?xml version=\"1.0\" "
    "encoding=\"UTF-8\"?><rootNode><child1>TestBody</child1><child2>TestBody2</child2></rootNode>";

struct sibling_text_capture {
    struct aws_byte_cursor capture1;
    struct aws_byte_cursor capture2;
    struct aws_byte_cursor node_name1;
    struct aws_byte_cursor node_name2;
};

int s_sibling_with_text_root_node(struct aws_xml_node *node, void *user_data) {
    struct sibling_text_capture *capture = user_data;

    struct aws_byte_cursor child1_name = aws_byte_cursor_from_c_str("child1");
    struct aws_byte_cursor child2_name = aws_byte_cursor_from_c_str("child2");

    struct aws_byte_cursor node_name = aws_xml_node_get_name(node);

    if (aws_byte_cursor_eq_ignore_case(&node_name, &child1_name)) {
        capture->node_name1 = node_name;
        if (aws_xml_node_as_body(node, &capture->capture1)) {
            return AWS_OP_ERR;
        }
    } else if (aws_byte_cursor_eq_ignore_case(&node_name, &child2_name)) {
        capture->node_name2 = node_name;
        if (aws_xml_node_as_body(node, &capture->capture2)) {
            return AWS_OP_ERR;
        }
    }

    return AWS_OP_SUCCESS;
}

int s_root_with_child_siblings(struct aws_xml_node *node, void *user_data) {
    return aws_xml_node_traverse(node, s_sibling_with_text_root_node, user_data);
}

static int s_xml_parser_siblings_with_text_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct sibling_text_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(siblings_with_text),
        .on_root_encountered = s_root_with_child_siblings,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name1[] = "child1";
    const char expected_value1[] = "TestBody";

    const char expected_name2[] = "child2";
    const char expected_value2[] = "TestBody2";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name1, sizeof(expected_name1) - 1, capture.node_name1.ptr, capture.node_name1.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value1, sizeof(expected_value1) - 1, capture.capture1.ptr, capture.capture1.len);

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name2, sizeof(expected_name2) - 1, capture.node_name2.ptr, capture.node_name2.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value2, sizeof(expected_value2) - 1, capture.capture2.ptr, capture.capture2.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_siblings_with_text, s_xml_parser_siblings_with_text_test)

const char *preamble_and_attributes =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
    "<!DOCTYPE html \n"
    " PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n"
    "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\"> "
    "<rootNode attribute1=\"abc\" attribute2=\"def\">\n"
    "<child1>TestBody</child1><child2 attribute3=\"childAttr\">TestBody2</child2></rootNode>";

struct preamble_and_attributes_capture {
    struct aws_byte_cursor capture1;
    struct aws_byte_cursor capture2;
    struct aws_xml_attribute capture2_attr;
    struct aws_byte_cursor node_name1;
    struct aws_byte_cursor node_name2;
    struct aws_xml_attribute root_attr1;
    struct aws_xml_attribute root_attr2;
};

int s_preamble_and_attributes_child_node(struct aws_xml_node *node, void *user_data) {
    struct preamble_and_attributes_capture *capture = user_data;

    struct aws_byte_cursor child1_name = aws_byte_cursor_from_c_str("child1");
    struct aws_byte_cursor child2_name = aws_byte_cursor_from_c_str("child2");

    struct aws_byte_cursor node_name = aws_xml_node_get_name(node);

    if (aws_byte_cursor_eq_ignore_case(&node_name, &child1_name)) {
        capture->node_name1 = node_name;
        if (aws_xml_node_as_body(node, &capture->capture1)) {
            return AWS_OP_ERR;
        }
    } else if (aws_byte_cursor_eq_ignore_case(&node_name, &child2_name)) {
        capture->node_name2 = node_name;
        if (aws_xml_node_as_body(node, &capture->capture2)) {
            return AWS_OP_ERR;
        }

        ASSERT_TRUE(aws_xml_node_get_num_attributes(node) == 1);

        capture->capture2_attr = aws_xml_node_get_attribute(node, 0);
    }

    return AWS_OP_SUCCESS;
}

int s_preamble_and_attributes(struct aws_xml_node *node, void *user_data) {
    struct preamble_and_attributes_capture *capture = user_data;

    ASSERT_TRUE(aws_xml_node_get_num_attributes(node) == 2);

    capture->root_attr1 = aws_xml_node_get_attribute(node, 0);
    capture->root_attr2 = aws_xml_node_get_attribute(node, 1);
    return aws_xml_node_traverse(node, s_preamble_and_attributes_child_node, user_data);
}

static int s_xml_parser_preamble_and_attributes_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct preamble_and_attributes_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(preamble_and_attributes),
        .on_root_encountered = s_preamble_and_attributes,
        .user_data = &capture,
    };

    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_attr1_name[] = "attribute1";
    const char expected_attr1_value1[] = "abc";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr1_name, sizeof(expected_attr1_name) - 1, capture.root_attr1.name.ptr, capture.root_attr1.name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr1_value1,
        sizeof(expected_attr1_value1) - 1,
        capture.root_attr1.value.ptr,
        capture.root_attr1.value.len);

    const char expected_attr2_name[] = "attribute2";
    const char expected_attr2_value1[] = "def";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr2_name, sizeof(expected_attr2_name) - 1, capture.root_attr2.name.ptr, capture.root_attr2.name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr2_value1,
        sizeof(expected_attr2_value1) - 1,
        capture.root_attr2.value.ptr,
        capture.root_attr2.value.len);

    const char expected_name1[] = "child1";
    const char expected_value1[] = "TestBody";

    const char expected_name2[] = "child2";
    const char expected_value2[] = "TestBody2";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name1, sizeof(expected_name1) - 1, capture.node_name1.ptr, capture.node_name1.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value1, sizeof(expected_value1) - 1, capture.capture1.ptr, capture.capture1.len);

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name2, sizeof(expected_name2) - 1, capture.node_name2.ptr, capture.node_name2.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value2, sizeof(expected_value2) - 1, capture.capture2.ptr, capture.capture2.len);

    const char expected_attr3_name[] = "attribute3";
    const char expected_attr3_value1[] = "childAttr";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr3_name,
        sizeof(expected_attr2_name) - 1,
        capture.capture2_attr.name.ptr,
        capture.capture2_attr.name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_attr3_value1,
        sizeof(expected_attr3_value1) - 1,
        capture.capture2_attr.value.ptr,
        capture.capture2_attr.value.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_preamble_and_attributes, s_xml_parser_preamble_and_attributes_test)

const char *nested_nodes_same_name_doc = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                                         "<!DOCTYPE html \n"
                                         " PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n"
                                         "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\"> "
                                         "<Node>\n"
                                         "    <Node>\n"
                                         "        <Node>\n"
                                         "            <Node>TestBody</Node>\n"
                                         "        </Node>\n"
                                         "     </Node>\n"
                                         "     <Node>\n"
                                         "         <Node>TestBody2</Node>\n"
                                         "     </Node>\n"
                                         "</Node>";

struct nested_node_capture {
    struct aws_byte_cursor node_body;
};

int s_nested_node(struct aws_xml_node *node, void *user_data) {
    struct nested_node_capture *capture = user_data;

    return aws_xml_node_as_body(node, &capture->node_body);
}

static int s_xml_parser_nested_node_same_name_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(nested_nodes_same_name_doc),
        .on_root_encountered = s_nested_node,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char *expected_body = "\n    <Node>\n"
                                "        <Node>\n"
                                "            <Node>TestBody</Node>\n"
                                "        </Node>\n"
                                "     </Node>\n"
                                "     <Node>\n"
                                "         <Node>TestBody2</Node>\n"
                                "     </Node>\n";

    ASSERT_BIN_ARRAYS_EQUALS(expected_body, strlen(expected_body), capture.node_body.ptr, capture.node_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_nested_node_same_name_test, s_xml_parser_nested_node_same_name_test)

const char *nested_nodes_deep_recursion_doc = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                                              "<!DOCTYPE html \n"
                                              " PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n"
                                              "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\"> "
                                              "<Node>\n"
                                              "    <Node>\n"
                                              "        <Node></Node>\n"
                                              "    </Node>\n"
                                              "</Node>";

int s_nested_node_deep_recursion(struct aws_xml_node *node, void *user_data) {
    return aws_xml_node_traverse(node, s_nested_node_deep_recursion, user_data);
}

static int s_xml_parser_nested_node_deep_recursion_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(nested_nodes_deep_recursion_doc),
        .max_depth = 2,
        .on_root_encountered = s_nested_node_deep_recursion,
        .user_data = NULL,
    };
    ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_xml_parse(allocator, &options));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_nested_node_deep_recursion_test, s_xml_parser_nested_node_deep_recursion_test)

const char *too_many_attributes = "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                                  "<!DOCTYPE html \n"
                                  " PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n"
                                  "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\"> "
                                  "<rootNode attribute1=\"abc\" attribute2=\"def\" attribute3=\"def\" "
                                  "attribute4=\"def\" attribute5=\"def\" attribute6=\"def\" attribute7=\"def\" "
                                  "attribute8=\"def\" attribute9=\"def\" attribute10=\"def\" attribute11=\"def\">\n"
                                  "</rootNode>";

int s_too_many_attributes(struct aws_xml_node *node, void *user_data) {
    (void)node;
    (void)user_data;
    return AWS_OP_SUCCESS;
}

static int s_xml_parser_too_many_attributes_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(too_many_attributes),
        .on_root_encountered = s_too_many_attributes,
        .user_data = NULL,
    };
    ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_xml_parse(allocator, &options));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_too_many_attributes_test, s_xml_parser_too_many_attributes_test)

const char *node_name_too_long =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
    "<!DOCTYPE html \n"
    " PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\"\n"
    "\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\"> "
    "<abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghi"
    "jklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrs"
    "tuvwxyzabcdefghijklmnopqrstuvwxyz>"
    "</"
    "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghij"
    "klmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrst"
    "uvwxyzabcdefghijklmnopqrstuvwxyz>";

int s_too_long(struct aws_xml_node *node, void *user_data) {
    (void)node;
    (void)user_data;
    return AWS_OP_SUCCESS;
}

static int s_xml_parser_name_too_long_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(node_name_too_long),
        .on_root_encountered = s_too_long,
        .user_data = NULL,
    };
    ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_xml_parse(allocator, &options));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_name_too_long_test, s_xml_parser_name_too_long_test)
