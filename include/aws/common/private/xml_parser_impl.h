#ifndef AWS_COMMON_XML_PARSER_IMPL_H
#define AWS_COMMON_XML_PARSER_IMPL_H

#include <aws/common/xml_parser.h>

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

#endif /* AWS_COMMON_XML_PARSER_IMPL_H */
