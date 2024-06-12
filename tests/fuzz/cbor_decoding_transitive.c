/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cbor.h>
#include <math.h>

/* NOLINTNEXTLINE(readability-identifier-naming) */
int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    struct aws_allocator *allocator = aws_mem_tracer_new(aws_default_allocator(), NULL, AWS_MEMTRACE_BYTES, 0);
    struct aws_byte_cursor input = aws_byte_cursor_from_array(data, size);
    aws_common_library_init(allocator);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, input);
    union {
        uint64_t unsigned_val;
        uint64_t neg_val;
        double double_val;
        uint64_t tag_val;
        bool boolean_val;
        struct aws_byte_cursor str_val;
        struct aws_byte_cursor bytes_val;
        uint64_t map_start;
        uint64_t array_start;
    } cbor_data;

    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
    while (aws_cbor_decoder_peek_type(decoder, &out_type) == AWS_OP_SUCCESS) {
        switch (out_type) {
            case AWS_CBOR_TYPE_UINT:
                AWS_FATAL_ASSERT(
                    aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &cbor_data.unsigned_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_NEGINT:
                AWS_FATAL_ASSERT(
                    aws_cbor_decoder_pop_next_negative_int_val(decoder, &cbor_data.neg_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_FLOAT:
                AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_float_val(decoder, &cbor_data.double_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_BYTES:
                AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_bytes_val(decoder, &cbor_data.bytes_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_TEXT:
                AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_text_val(decoder, &cbor_data.str_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_ARRAY_START:
                AWS_FATAL_ASSERT(
                    aws_cbor_decoder_pop_next_array_start(decoder, &cbor_data.array_start) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_MAP_START:
                AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_map_start(decoder, &cbor_data.map_start) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_TAG:
                AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_tag_val(decoder, &cbor_data.tag_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_BOOL:
                AWS_FATAL_ASSERT(
                    aws_cbor_decoder_pop_next_boolean_val(decoder, &cbor_data.boolean_val) == AWS_OP_SUCCESS);
                break;
            case AWS_CBOR_TYPE_NULL:
            case AWS_CBOR_TYPE_UNDEFINED:
            case AWS_CBOR_TYPE_BREAK:
            case AWS_CBOR_TYPE_INDEF_BYTES_START:
            case AWS_CBOR_TYPE_INDEF_TEXT_START:
            case AWS_CBOR_TYPE_INDEF_ARRAY_START:
            case AWS_CBOR_TYPE_INDEF_MAP_START: {
                enum aws_cbor_type type = AWS_CBOR_TYPE_UNKNOWN;
                AWS_FATAL_ASSERT(aws_cbor_decoder_peek_type(decoder, &type) == AWS_OP_SUCCESS);
                AWS_FATAL_ASSERT(type == out_type);
                AWS_FATAL_ASSERT(aws_cbor_decoder_consume_next_single_element(decoder) == AWS_OP_SUCCESS);
            } break;

            default:
                break;
        }
    }
    aws_cbor_decoder_destroy(decoder);

    atexit(aws_common_library_clean_up);

    /* Check for leaks */
    AWS_FATAL_ASSERT(aws_mem_tracer_count(allocator) == 0);
    allocator = aws_mem_tracer_destroy(allocator);
    return 0;
}
