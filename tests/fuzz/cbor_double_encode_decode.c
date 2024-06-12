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
    double val = 0;
    if (!aws_byte_cursor_read_float_be64(&input, &val)) {
        allocator = aws_mem_tracer_destroy(allocator);
        /* Ignore the invalid double */
        return 0;
    }
    aws_common_library_init(allocator);
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_float(encoder, val);

    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
    AWS_FATAL_ASSERT(aws_cbor_decoder_peek_type(decoder, &out_type) == 0);
    switch (out_type) {
        case AWS_CBOR_TYPE_UINT: {
            uint64_t result = 0;
            AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &result) == 0);
            AWS_FATAL_ASSERT((double)result == val);
            break;
        }
        case AWS_CBOR_TYPE_NEGINT: {
            uint64_t result = 0;
            AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_negative_int_val(decoder, &result) == 0);
            int64_t expected_val = -1 - result;
            AWS_FATAL_ASSERT(expected_val == (int64_t)val);
            break;
        }
        case AWS_CBOR_TYPE_FLOAT: {
            double result = 0;
            AWS_FATAL_ASSERT(aws_cbor_decoder_pop_next_float_val(decoder, &result) == 0);
            if (isnan(val)) {
                AWS_FATAL_ASSERT(isnan(result));
            } else {
                AWS_FATAL_ASSERT(result == val);
            }
            break;
        }

        default:
            AWS_FATAL_ASSERT(false);
            break;
    }
    AWS_FATAL_ASSERT(aws_cbor_decoder_get_remaining_length(decoder) == 0);
    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);

    atexit(aws_common_library_clean_up);

    /* Check for leaks */
    AWS_FATAL_ASSERT(aws_mem_tracer_count(allocator) == 0);
    allocator = aws_mem_tracer_destroy(allocator);
    return 0;
}
