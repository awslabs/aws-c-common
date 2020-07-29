#ifndef AWS_COMMON_XML_PARSER
#define AWS_COMMON_XML_PARSER

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/array_list.h>
#include <aws/common/byte_buf.h>

#include <aws/common/exports.h>

struct aws_xml_attribute {
    struct aws_byte_cursor name;
    struct aws_byte_cursor value;
};

struct aws_xml_node {
    struct aws_byte_cursor name;
    struct aws_array_list attributes;
    struct aws_byte_cursor doc_at_body;
    bool processed;
};

struct aws_xml_parser;

/**
 * Callback for when an xml node is encountered in the document. As a user you have a few options:
 *
 * 1. reject the document parsing at this point by returning false. This will immediately stop doc parsing.
 * 2. call aws_xml_node_traverse() on the node to descend into the node with a new callback and user_data.
 * 3. call aws_xml_node_as_body() to retrieve the contents of the node as text.
 *
 * return true to continue the parsing operation.
 */
typedef bool(
    aws_xml_parser_on_node_encountered_fn)(struct aws_xml_parser *parser, struct aws_xml_node *node, void *user_data);

struct aws_xml_parser {
    struct aws_allocator *allocator;
    struct aws_byte_cursor doc;
    struct aws_array_list callback_stack;
    /* maximum of 10 attributes */
    struct aws_xml_attribute attributes[10];
    /* splits on attributes and node name, so (10 attributes + 1 name) */
    struct aws_byte_cursor split_scratch[11];
    size_t max_depth;
    int error;
    bool stop_parsing;
};

AWS_EXTERN_C_BEGIN

/**
 * Initialize the parser with xml document: doc.
 */
AWS_COMMON_API
int aws_xml_parser_init(
    struct aws_xml_parser *parser,
    struct aws_allocator *allocator,
    struct aws_byte_cursor *doc,
    size_t max_depth);

AWS_COMMON_API
void aws_xml_parser_clean_up(struct aws_xml_parser *parser);

/**
 * Parse the doc until the end or until a callback rejects the document.
 * on_node_encountered will be invoked when the root node is encountered.
 */
AWS_COMMON_API
int aws_xml_parser_parse(
    struct aws_xml_parser *parser,
    aws_xml_parser_on_node_encountered_fn *on_node_encountered,
    void *user_data);

/**
 * Writes the contents of the body of node into out_body. out_body is an output parameter in this case. Upon success,
 * out_body will contain the body of the node.
 */
AWS_COMMON_API
int aws_xml_node_as_body(struct aws_xml_parser *parser, struct aws_xml_node *node, struct aws_byte_cursor *out_body);

/**
 * Traverse node and invoke on_node_encountered when a nested node is encountered.
 */
AWS_COMMON_API
int aws_xml_node_traverse(
    struct aws_xml_parser *parser,
    struct aws_xml_node *node,
    aws_xml_parser_on_node_encountered_fn *on_node_encountered,
    void *user_data);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_XML_PARSER */
