/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/clock.h>
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

const char *s_empty_element_name_doc =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?><rootNode><><child1>TestBody</child1></rootNode>";

static int s_xml_parser_empty_element_name_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct child_text_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(s_empty_element_name_doc),
        .on_root_encountered = s_root_with_child,
        .user_data = &capture,
    };
    ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_xml_parse(allocator, &options));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_empty_element_name_test, s_xml_parser_empty_element_name_test)

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

const char *siblings_with_empty_tag = "<?xml version=\"1.0\" "
                                      "encoding=\"UTF-8\"?><rootNode><child1 /><child2>TestBody2</child2></rootNode>";

static int s_xml_parser_child_empty_tag(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct sibling_text_capture capture;
    AWS_ZERO_STRUCT(capture);

    capture.capture1 = aws_byte_cursor_from_c_str("random values");

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(siblings_with_empty_tag),
        .on_root_encountered = s_root_with_child_siblings,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name1[] = "child1";

    const char expected_name2[] = "child2";
    const char expected_value2[] = "TestBody2";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name1, sizeof(expected_name1) - 1, capture.node_name1.ptr, capture.node_name1.len);
    ASSERT_PTR_EQUALS(capture.capture1.ptr, NULL);
    ASSERT_UINT_EQUALS(capture.capture1.len, 0);

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_name2, sizeof(expected_name2) - 1, capture.node_name2.ptr, capture.node_name2.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_value2, sizeof(expected_value2) - 1, capture.capture2.ptr, capture.capture2.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_child_empty_tag, s_xml_parser_child_empty_tag)

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

static int s_xml_parser_unescape_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    enum { num_cases = 5 };

    struct aws_byte_cursor input[num_cases] = {
        aws_byte_cursor_from_c_str("Au revoir, Shoshanna!"),
        aws_byte_cursor_from_c_str("quote1 &quot; quote2 &#34; quote3 &#x22; "
                                   "gt1 &gt; gt2 &#62; gt3 &#x3E; "
                                   "lt1 &lt; lt2 &#60; lt3 &#x3C; "
                                   "apos1 &apos; apos2 &#39; apos3 &#x27; "
                                   "amp1 &amp; amp2 &#38; amp3 &#x26;"),
        aws_byte_cursor_from_c_str("Say &apos;what&apos; again; Say &apos;what&apos; again..."),
        aws_byte_cursor_from_c_str("Hello &#x1F600;"),
        aws_byte_cursor_from_c_str("Hello &#128512;")};

    struct aws_byte_cursor expected[num_cases] = {
        aws_byte_cursor_from_c_str("Au revoir, Shoshanna!"),
        aws_byte_cursor_from_c_str("quote1 \" quote2 \" quote3 \" "
                                   "gt1 > gt2 > gt3 > "
                                   "lt1 < lt2 < lt3 < "
                                   "apos1 ' apos2 ' apos3 ' "
                                   "amp1 & amp2 & amp3 &"),
        aws_byte_cursor_from_c_str("Say 'what' again; Say 'what' again..."),
        aws_byte_cursor_from_c_str("Hello \xF0\x9F\x98\x80"),
        aws_byte_cursor_from_c_str("Hello \xF0\x9F\x98\x80")};

    for (size_t i = 0; i < num_cases; ++i) {
        struct aws_byte_buf out;
        aws_byte_buf_init(&out, allocator, 30);

        ASSERT_SUCCESS(aws_byte_buf_append_unescaped_xml(allocator, input[i], &out));

        ASSERT_BIN_ARRAYS_EQUALS(out.buffer, out.len, expected[i].ptr, expected[i].len);

        aws_byte_buf_clean_up(&out);
    }

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(xml_parser_unescape_test, s_xml_parser_unescape_test)

static int s_xml_parser_unescape_error_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    enum { num_cases = 7 };

    struct aws_byte_cursor input[num_cases] = {
        aws_byte_cursor_from_c_str("aaa &bbb c"),
        aws_byte_cursor_from_c_str("aaa &&quot; c"),
        aws_byte_cursor_from_c_str("aaa &quot123; c"),
        aws_byte_cursor_from_c_str("aaa &#; c"),
        aws_byte_cursor_from_c_str("aaa &#x; c"),
        aws_byte_cursor_from_c_str("aaa &#123456789987654321; c"),
        aws_byte_cursor_from_c_str("aaa &#x123456789987654321abcdef; c"),
    };

    for (size_t i = 0; i < num_cases; ++i) {
        struct aws_byte_buf out;
        aws_byte_buf_init(&out, allocator, 30);

        ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_byte_buf_append_unescaped_xml(allocator, input[i], &out));

        aws_byte_buf_clean_up(&out);
    }

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(xml_parser_unescape_error_test, s_xml_parser_unescape_error_test)

const char *child_with_text_escaped =
    "<?xml version=\"1.0\" encoding=\"UTF-8\"?><rootNode><child1>&quot;TestBody&quot;</child1></rootNode>";

struct child_text_buf_capture {
    struct aws_allocator *allocator;
    struct aws_byte_buf capture_buf;
    struct aws_byte_cursor node_name;
};

int s_child_with_text_root_node_escaped(struct aws_xml_node *node, void *user_data) {
    struct child_text_buf_capture *capture = user_data;
    if (aws_xml_node_as_body_unescaped(capture->allocator, node, &capture->capture_buf)) {
        return AWS_OP_ERR;
    }
    capture->node_name = aws_xml_node_get_name(node);

    return AWS_OP_SUCCESS;
}

int s_root_with_child_escaped(struct aws_xml_node *node, void *user_data) {
    if (aws_xml_node_traverse(node, s_child_with_text_root_node_escaped, user_data)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}

static int s_xml_parser_child_with_text_escaped_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    struct child_text_buf_capture capture;
    AWS_ZERO_STRUCT(capture);
    capture.allocator = allocator;
    aws_byte_buf_init(&capture.capture_buf, allocator, 30);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(child_with_text_escaped),
        .on_root_encountered = s_root_with_child_escaped,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child1";
    const char expected_value[] = "\"TestBody\"";

    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.node_name.ptr, capture.node_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_value, sizeof(expected_value) - 1, capture.capture_buf.buffer, capture.capture_buf.len);

    aws_byte_buf_clean_up(&capture.capture_buf);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_child_with_text_escaped, s_xml_parser_child_with_text_escaped_test)

/*
 * Verify that skipping <Owner> does not falsely match <OwnerId> as a nested same-name open.
 * The open-tag search must require a name-terminator after the tag name.
 */
const char *prefix_collision_doc = "<ListBucketResult>"
                                   "<Contents>"
                                   "<Owner><OwnerId>abc123</OwnerId><DisplayName>test</DisplayName></Owner>"
                                   "<Key>file.txt</Key>"
                                   "</Contents>"
                                   "</ListBucketResult>";

struct prefix_collision_capture {
    struct aws_byte_cursor owner_body;
    struct aws_byte_cursor key_body;
};

int s_prefix_collision_contents_child(struct aws_xml_node *node, void *user_data) {
    struct prefix_collision_capture *capture = user_data;
    struct aws_byte_cursor name = aws_xml_node_get_name(node);
    struct aws_byte_cursor owner_name = aws_byte_cursor_from_c_str("Owner");
    struct aws_byte_cursor key_name = aws_byte_cursor_from_c_str("Key");

    if (aws_byte_cursor_eq(&name, &owner_name)) {
        return aws_xml_node_as_body(node, &capture->owner_body);
    } else if (aws_byte_cursor_eq(&name, &key_name)) {
        return aws_xml_node_as_body(node, &capture->key_body);
    }
    return AWS_OP_SUCCESS;
}

int s_prefix_collision_contents(struct aws_xml_node *node, void *user_data) {
    return aws_xml_node_traverse(node, s_prefix_collision_contents_child, user_data);
}

int s_prefix_collision_root(struct aws_xml_node *node, void *user_data) {
    return aws_xml_node_traverse(node, s_prefix_collision_contents, user_data);
}

static int s_xml_parser_prefix_collision_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct prefix_collision_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(prefix_collision_doc),
        .on_root_encountered = s_prefix_collision_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_owner[] = "<OwnerId>abc123</OwnerId><DisplayName>test</DisplayName>";
    const char expected_key[] = "file.txt";

    ASSERT_BIN_ARRAYS_EQUALS(
        expected_owner, sizeof(expected_owner) - 1, capture.owner_body.ptr, capture.owner_body.len);
    ASSERT_BIN_ARRAYS_EQUALS(expected_key, sizeof(expected_key) - 1, capture.key_body.ptr, capture.key_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_prefix_collision_test, s_xml_parser_prefix_collision_test)

/*
 * Verify that true nested same-name elements (<a> inside <a>) and prefix-sharing
 * siblings (<ab> inside <a>) both parse correctly.
 */
const char *nested_same_name_with_prefix_children_doc = "<a><a>inner</a><ab>other</ab></a>";

struct nested_prefix_capture {
    struct aws_byte_cursor a_body;
};

int s_nested_prefix_root(struct aws_xml_node *node, void *user_data) {
    struct nested_prefix_capture *capture = user_data;
    return aws_xml_node_as_body(node, &capture->a_body);
}

static int s_xml_parser_nested_same_name_with_prefix_children_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct nested_prefix_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(nested_same_name_with_prefix_children_doc),
        .on_root_encountered = s_nested_prefix_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected[] = "<a>inner</a><ab>other</ab>";
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected) - 1, capture.a_body.ptr, capture.a_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(
    xml_parser_nested_same_name_with_prefix_children_test,
    s_xml_parser_nested_same_name_with_prefix_children_test)

/*
 * Verify that XML comments (<!-- ... -->) are skipped during child traversal.
 */
const char *comment_in_body_doc = "<root><!-- this is a comment --><child>value</child></root>";

struct comment_capture {
    struct aws_byte_cursor child_body;
    struct aws_byte_cursor child_name;
};

int s_comment_child(struct aws_xml_node *node, void *user_data) {
    struct comment_capture *capture = user_data;
    capture->child_name = aws_xml_node_get_name(node);
    return aws_xml_node_as_body(node, &capture->child_body);
}

int s_comment_root(struct aws_xml_node *node, void *user_data) {
    return aws_xml_node_traverse(node, s_comment_child, user_data);
}

static int s_xml_parser_comment_skipped_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct comment_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(comment_in_body_doc),
        .on_root_encountered = s_comment_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child";
    const char expected_value[] = "value";
    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.child_name.ptr, capture.child_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_value, sizeof(expected_value) - 1, capture.child_body.ptr, capture.child_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_comment_skipped_test, s_xml_parser_comment_skipped_test)

/*
 * Verify that CDATA sections (<![CDATA[...]]>) are skipped during child traversal.
 */
const char *cdata_in_body_doc = "<root><![CDATA[<not>an</element>]]><child>value</child></root>";

static int s_xml_parser_cdata_skipped_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct comment_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(cdata_in_body_doc),
        .on_root_encountered = s_comment_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child";
    const char expected_value[] = "value";
    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.child_name.ptr, capture.child_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_value, sizeof(expected_value) - 1, capture.child_body.ptr, capture.child_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_cdata_skipped_test, s_xml_parser_cdata_skipped_test)

/*
 * Verify that processing instructions (<?...?>) are skipped during child traversal.
 */
const char *pi_in_body_doc = "<root><?xml-stylesheet type=\"text/xsl\" href=\"style.xsl\"?><child>value</child></root>";

static int s_xml_parser_pi_skipped_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct comment_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(pi_in_body_doc),
        .on_root_encountered = s_comment_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child";
    const char expected_value[] = "value";
    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.child_name.ptr, capture.child_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_value, sizeof(expected_value) - 1, capture.child_body.ptr, capture.child_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_pi_skipped_test, s_xml_parser_pi_skipped_test)

/*
 * Verify that '>' inside a comment does not terminate the comment early
 * or cause subsequent content to be parsed as a sibling element.
 */
const char *comment_with_gt_doc = "<root><!-- contains > character --><child>safe</child></root>";

static int s_xml_parser_comment_with_gt_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct comment_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(comment_with_gt_doc),
        .on_root_encountered = s_comment_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected_name[] = "child";
    const char expected_value[] = "safe";
    ASSERT_BIN_ARRAYS_EQUALS(expected_name, sizeof(expected_name) - 1, capture.child_name.ptr, capture.child_name.len);
    ASSERT_BIN_ARRAYS_EQUALS(
        expected_value, sizeof(expected_value) - 1, capture.child_body.ptr, capture.child_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_comment_with_gt_test, s_xml_parser_comment_with_gt_test)

/*
 * Verify that parsing deeply nested same-name elements (N=20000) completes in O(N) time.
 * The test asserts the parse finishes within 2 seconds.
 */
static int s_xml_parser_nested_same_name_large_depth_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    /* Build: <a><a><a>...(20000 opens)...</a></a></a>...(20000 closes) */
    const size_t depth = 20000;
    struct aws_byte_buf doc_buf;
    aws_byte_buf_init(&doc_buf, allocator, depth * 10);

    struct aws_byte_cursor a_open = aws_byte_cursor_from_c_str("<a>");
    struct aws_byte_cursor a_close = aws_byte_cursor_from_c_str("</a>");

    for (size_t i = 0; i < depth; i++) {
        aws_byte_buf_append_dynamic(&doc_buf, &a_open);
    }
    for (size_t i = 0; i < depth; i++) {
        aws_byte_buf_append_dynamic(&doc_buf, &a_close);
    }

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_buf(&doc_buf),
        .on_root_encountered = s_nested_node,
        .user_data = &capture,
    };

    uint64_t start_ns = 0;
    aws_high_res_clock_get_ticks(&start_ns);

    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    uint64_t end_ns = 0;
    aws_high_res_clock_get_ticks(&end_ns);

    uint64_t elapsed_ms = (end_ns - start_ns) / 1000000;
    ASSERT_TRUE(
        elapsed_ms < 2000,
        "xml parse took %llu ms — expected < 2000 ms with depth=%zu",
        (unsigned long long)elapsed_ms,
        depth);

    ASSERT_TRUE(capture.node_body.len > 0);

    aws_byte_buf_clean_up(&doc_buf);
    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_nested_same_name_large_depth_test, s_xml_parser_nested_same_name_large_depth_test)

/*
 * Verify that self-closing tags (<a/>) inside <a> do not increment depth count.
 */
const char *self_closing_same_name_doc = "<a><a/>inner</a>";

static int s_xml_parser_self_closing_same_name_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(self_closing_same_name_doc),
        .on_root_encountered = s_nested_node,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected[] = "<a/>inner";
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected) - 1, capture.node_body.ptr, capture.node_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_self_closing_same_name_test, s_xml_parser_self_closing_same_name_test)

/*
 * Verify that a close tag inside CDATA is not treated as the real close tag.
 */
const char *cdata_false_close_doc = "<data><![CDATA[</data>]]>real</data>";

int s_cdata_false_close_root(struct aws_xml_node *node, void *user_data) {
    struct nested_node_capture *capture = user_data;
    return aws_xml_node_as_body(node, &capture->node_body);
}

static int s_xml_parser_cdata_false_close_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(cdata_false_close_doc),
        .on_root_encountered = s_cdata_false_close_root,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected[] = "<![CDATA[</data>]]>real";
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected) - 1, capture.node_body.ptr, capture.node_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_cdata_false_close_test, s_xml_parser_cdata_false_close_test)

/*
 * Verify that an open tag inside a comment does not cause depth increment.
 */
const char *comment_false_open_doc = "<tag><!-- <tag> -->body</tag>";

static int s_xml_parser_comment_false_open_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(comment_false_open_doc),
        .on_root_encountered = s_nested_node,
        .user_data = &capture,
    };
    ASSERT_SUCCESS(aws_xml_parse(allocator, &options));

    const char expected[] = "<!-- <tag> -->body";
    ASSERT_BIN_ARRAYS_EQUALS(expected, sizeof(expected) - 1, capture.node_body.ptr, capture.node_body.len);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_comment_false_open_test, s_xml_parser_comment_false_open_test)

/*
 * Verify that a document ending with a bare '<' does not crash (out-of-bounds read).
 */
static int s_xml_parser_trailing_open_bracket_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    const char *doc = "<a><";

    struct nested_node_capture capture;
    AWS_ZERO_STRUCT(capture);

    struct aws_xml_parser_options options = {
        .doc = aws_byte_cursor_from_c_str(doc),
        .on_root_encountered = s_nested_node,
        .user_data = &capture,
    };
    ASSERT_ERROR(AWS_ERROR_INVALID_XML, aws_xml_parse(allocator, &options));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(xml_parser_trailing_open_bracket_test, s_xml_parser_trailing_open_bracket_test)
