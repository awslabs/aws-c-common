/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/big.h>
#include <aws/common/cbor.h>
#include <aws/common/encoding.h>
#include <float.h>
#include <math.h>

#include <aws/testing/aws_test_harness.h>

#define CBOR_TEST_CASE(NAME)                                                                                           \
    AWS_TEST_CASE(NAME, s_test_##NAME);                                                                                \
    static int s_test_##NAME(struct aws_allocator *allocator, void *ctx)

CBOR_TEST_CASE(cbor_encode_decode_int_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    enum { VALUE_NUM = 6 };

    /**
     * Less than 24 only take 1 byte,
     * 24 to uint8_t max takes 2 bytes
     * uint8_t max to uint16_t max takes 3 bytes
     * uint16_t max to uint32_t maxx takes 5 bytes
     * uint32_t max to uint64_t max takes 9 bytes
     */
    uint64_t values[VALUE_NUM] = {23, 24, UINT8_MAX + 1, UINT16_MAX + 1U, UINT32_MAX + 1LLU, UINT64_MAX};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 2, 3, 5, 9, 9};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    /* Unsigned int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_uint(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    /* Negative int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_negint(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    /* Unsigned int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        uint64_t result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }
    /* Negative int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        uint64_t result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_negative_int_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_double_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);

    struct double_test_case {
        double value;
        size_t expected_encoded_len;
        enum aws_cbor_type expected_type;
        const char *comment;
    };
    struct double_test_case cases[] = {
        {1.0, 1, AWS_CBOR_TYPE_UINT, "1 fits an unsigned int"},
        {-1.0, 1, AWS_CBOR_TYPE_NEGINT, "-1 fits a negative int"},
        {1.1, 9, AWS_CBOR_TYPE_FLOAT, "1.1 is not float-representable, stays a double"},
        {1.1f, 5, AWS_CBOR_TYPE_FLOAT, "1.1f is float-representable"},
        {-1.1f, 5, AWS_CBOR_TYPE_FLOAT, "-1.1f is float-representable"},
        {INFINITY, 5, AWS_CBOR_TYPE_FLOAT, "INFINITY encodes as a float"},
        {FLT_MAX, 5, AWS_CBOR_TYPE_FLOAT, "FLT_MAX is float-representable"},
        {DBL_MAX, 9, AWS_CBOR_TYPE_FLOAT, "DBL_MAX stays a double"},
        {DBL_MIN, 9, AWS_CBOR_TYPE_FLOAT, "DBL_MIN stays a double"},
        {HUGE_VAL, 5, AWS_CBOR_TYPE_FLOAT, "HUGE_VAL (infinity) encodes as a float"},
        {0x1p63, 5, AWS_CBOR_TYPE_FLOAT, "2^63 is out of the 32-bit integer range, float-representable"},
        {(double)UINT32_MAX, 5, AWS_CBOR_TYPE_UINT, "UINT32_MAX is the upper bound of the 32-bit integer range"},
        {0x1p32, 5, AWS_CBOR_TYPE_FLOAT, "2^32 is just past UINT32_MAX, float-representable"},
        {-0x1p32, 5, AWS_CBOR_TYPE_NEGINT, "-2^32 is the lowest value in the 32-bit integer range"},
        {-0x1p33, 5, AWS_CBOR_TYPE_FLOAT, "-2^33 is just past -2^32, float-representable"},
        {0x1p32 + 1, 9, AWS_CBOR_TYPE_FLOAT, "2^32+1 is past UINT32_MAX and not float-representable, stays a double"},
        {-0x1p32 - 1,
         9,
         AWS_CBOR_TYPE_FLOAT,
         "-2^32-1 is below the 32-bit integer range and not float-representable, stays a double"},
    };
    size_t case_num = AWS_ARRAY_SIZE(cases);

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    for (size_t i = 0; i < case_num; i++) {
        aws_cbor_encoder_write_float(encoder, cases[i].value);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + cases[i].expected_encoded_len, cursor.len, cases[i].comment);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    for (size_t i = 0; i < case_num; i++) {
        enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
        ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
        ASSERT_UINT_EQUALS(cases[i].expected_type, out_type, "%s", cases[i].comment);
        switch (cases[i].expected_type) {
            case AWS_CBOR_TYPE_UINT: {
                uint64_t result = 0;
                ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &result));
                ASSERT_TRUE(cases[i].value == (double)result, "%s", cases[i].comment);
                break;
            }
            case AWS_CBOR_TYPE_NEGINT: {
                uint64_t result = 0;
                ASSERT_SUCCESS(aws_cbor_decoder_pop_next_negative_int_val(decoder, &result));
                /* Negative int is encoded as -1 - value. */
                ASSERT_TRUE((-1 - cases[i].value) == (double)result, "%s", cases[i].comment);
                break;
            }
            case AWS_CBOR_TYPE_FLOAT: {
                double result = 0;
                ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &result));
                ASSERT_TRUE(cases[i].value == result, "%s", cases[i].comment);
                break;
            }
            default:
                ASSERT_TRUE(false, "unexpected cbor type for %s", cases[i].comment);
        }
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_bool_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    enum { VALUE_NUM = 2 };
    bool values[VALUE_NUM] = {true, false};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 1};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_bool(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        bool result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_boolean_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_bytesstr_str_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    enum { VALUE_NUM = 2 };
    struct aws_byte_cursor values[VALUE_NUM] = {val_1, val_2};
    uint64_t expected_encoded_len[VALUE_NUM] = {1 + val_1.len, 1 + val_2.len};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_text(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_bytes(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_text_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, &values[i]));
    }
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_bytes_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, &values[i]));
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_array_map_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    enum { VALUE_NUM = 2 };
    struct aws_byte_cursor values[VALUE_NUM] = {val_1, val_2};
    uint64_t expected_encoded_len[VALUE_NUM] = {1 + val_1.len, 1 + val_2.len};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);

    /* Array with 2 elements */
    aws_cbor_encoder_write_array_start(encoder, 2);
    struct aws_byte_cursor encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* Array start with 2 element only takes 1 byte */
    ASSERT_UINT_EQUALS(encoded_len + 1, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_text(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }

    /* Map with 1 element */
    aws_cbor_encoder_write_map_start(encoder, 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* Map start with 1 (key, value pair) only takes 1 byte */
    ASSERT_UINT_EQUALS(encoded_len + 1, encoded_cursor.len);
    encoded_len = encoded_cursor.len;
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_bytes(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }

    /* Map with a lot element, not closure. */
    aws_cbor_encoder_write_array_start(encoder, UINT16_MAX + 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* The size takes 4 bytes and one more for the cbor start item */
    ASSERT_UINT_EQUALS(encoded_len + 5, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    aws_cbor_encoder_write_map_start(encoder, UINT16_MAX + 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* The size takes 4 bytes and one more for the cbor start item */
    ASSERT_UINT_EQUALS(encoded_len + 5, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);

    uint64_t element_size = 0;
    aws_cbor_decoder_pop_next_array_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, 2);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_text_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, &values[i]));
    }
    aws_cbor_decoder_pop_next_map_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, 1);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decoder_pop_next_bytes_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, &values[i]));
    }
    /* 65536 exceeds the decoder's max container size limit (10000) */
    ASSERT_FAILS(aws_cbor_decoder_pop_next_array_start(decoder, &element_size));
    ASSERT_INT_EQUALS(AWS_ERROR_CBOR_RESOURCE_LIMIT_EXCEEDED, aws_last_error());
    /* Decoder is now in error state, reset to continue */
    aws_cbor_decoder_reset_src(decoder, (struct aws_byte_cursor){0});

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_simple_value_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_null(encoder);
    aws_cbor_encoder_write_undefined(encoder);
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* in total 2 bytes for two simple value */
    ASSERT_UINT_EQUALS(2, final_cursor.len);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);

    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, AWS_CBOR_TYPE_NULL);
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_single_element(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, AWS_CBOR_TYPE_UNDEFINED);
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_single_element(decoder));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

/* Test a complicate multiple stacks encode and decode */
CBOR_TEST_CASE(cbor_encode_decode_indef_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);

    /* Create a non-sense stack of inf collections. */
    aws_cbor_encoder_write_indef_map_start(encoder);
    /* Key */
    aws_cbor_encoder_write_text(encoder, val_1);
    /* Value */
    aws_cbor_encoder_write_indef_array_start(encoder);
    /* element 1 in array */
    aws_cbor_encoder_write_indef_text_start(encoder);
    aws_cbor_encoder_write_text(encoder, val_1);
    aws_cbor_encoder_write_text(encoder, val_2);
    aws_cbor_encoder_write_break(encoder);
    /* element 2 in array */
    aws_cbor_encoder_write_indef_bytes_start(encoder);
    aws_cbor_encoder_write_bytes(encoder, val_1);
    aws_cbor_encoder_write_bytes(encoder, val_2);
    aws_cbor_encoder_write_break(encoder);
    /* element 3 as a tag in array */
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_DECIMAL_FRACTION);
    aws_cbor_encoder_write_indef_array_start(encoder);
    aws_cbor_encoder_write_indef_bytes_start(encoder);
    aws_cbor_encoder_write_bytes(encoder, val_1);
    aws_cbor_encoder_write_bytes(encoder, val_2);
    aws_cbor_encoder_write_break(encoder);
    aws_cbor_encoder_write_break(encoder);
    /* Closure for the array */
    aws_cbor_encoder_write_break(encoder);
    /* Closure for the map */
    aws_cbor_encoder_write_break(encoder);

    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);

    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, AWS_CBOR_TYPE_INDEF_MAP_START);

    /* Get rid of the whole inf map with all the data content */
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_error_handling_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    /* Major type 7 with argument 30, 11111110, malformed CBOR */
    uint8_t invalid_data[] = {0xFE};
    struct aws_byte_cursor invalid_cbor = aws_byte_cursor_from_array(invalid_data, sizeof(invalid_data));

    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;

    /* 1. Malformed cbor data */
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, invalid_cbor);
    ASSERT_FAILS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());

    /* 2. Empty cursor */
    struct aws_byte_cursor empty = {0};
    aws_cbor_decoder_reset_src(decoder, empty);
    ASSERT_FAILS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());

    /* 3. Try get wrong type */
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    uint64_t val = 1;
    aws_cbor_encoder_write_uint(encoder, val);
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    aws_cbor_decoder_reset_src(decoder, final_cursor);
    uint64_t out = 0;
    ASSERT_FAILS(aws_cbor_decoder_pop_next_array_start(decoder, &out));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    /* But, we can still keep decoding for the right type */
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &out));
    ASSERT_UINT_EQUALS(val, out);
    /* All the data has been consumed, now it's invalid */
    ASSERT_FAILS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_FAILS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());

    /* 4. Consume data items with size */
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    aws_cbor_encoder_reset(encoder);
    aws_cbor_encoder_write_map_start(encoder, 1);
    /* Key */
    aws_cbor_encoder_write_text(encoder, val_1);
    /* Value */
    aws_cbor_encoder_write_array_start(encoder, 1);
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_NEGATIVE_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, val_1);
    final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    aws_cbor_decoder_reset_src(decoder, final_cursor);
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_CBOR_TYPE_MAP_START, out_type);
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_decoder_destroy(decoder);
    aws_cbor_encoder_destroy(encoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_resource_limit_container_size_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    /* Encode an array header declaring 10001 elements (exceeds the 10000 limit) */
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_array_start(encoder, 10001);
    struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, cursor);
    uint64_t out_size = 0;
    ASSERT_FAILS(aws_cbor_decoder_pop_next_array_start(decoder, &out_size));
    ASSERT_INT_EQUALS(AWS_ERROR_CBOR_RESOURCE_LIMIT_EXCEEDED, aws_last_error());

    /* Same for map */
    aws_cbor_encoder_reset(encoder);
    aws_cbor_encoder_write_map_start(encoder, 10001);
    cursor = aws_cbor_encoder_get_encoded_data(encoder);
    aws_cbor_decoder_reset_src(decoder, cursor);
    ASSERT_FAILS(aws_cbor_decoder_pop_next_map_start(decoder, &out_size));
    ASSERT_INT_EQUALS(AWS_ERROR_CBOR_RESOURCE_LIMIT_EXCEEDED, aws_last_error());

    /* Verify 10000 is still accepted */
    aws_cbor_encoder_reset(encoder);
    aws_cbor_encoder_write_array_start(encoder, 10000);
    cursor = aws_cbor_encoder_get_encoded_data(encoder);
    aws_cbor_decoder_reset_src(decoder, cursor);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_array_start(decoder, &out_size));
    ASSERT_UINT_EQUALS(10000, out_size);

    aws_cbor_decoder_destroy(decoder);
    aws_cbor_encoder_destroy(encoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_resource_limit_depth_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    /* Build 129 nested arrays of length 1: 0x81 repeated 129 times, then 0x01.
     * This requires depth 130 which exceeds the limit of 128. */
    uint8_t data[130];
    memset(data, 0x81, 129); /* array of 1 element, 129 times */
    data[129] = 0x01;        /* innermost value: uint 1 */
    struct aws_byte_cursor cursor = aws_byte_cursor_from_array(data, sizeof(data));

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, cursor);
    ASSERT_FAILS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_INT_EQUALS(AWS_ERROR_CBOR_RESOURCE_LIMIT_EXCEEDED, aws_last_error());

    /* Verify 127 nested arrays + 1 uint (128 total calls, max depth = 128) is accepted */
    uint8_t ok_data[128];
    memset(ok_data, 0x81, 127); /* 127 arrays of 1 element */
    ok_data[127] = 0x01;        /* innermost value: uint 1 */
    cursor = aws_byte_cursor_from_array(ok_data, sizeof(ok_data));
    aws_cbor_decoder_reset_src(decoder, cursor);
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));

    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_remaining_length_after_peek_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_uint(encoder, 42);
    aws_cbor_encoder_write_uint(encoder, 100);
    struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
    size_t total_len = cursor.len;

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, cursor);
    ASSERT_UINT_EQUALS(total_len, aws_cbor_decoder_get_remaining_length(decoder));
    ASSERT_UINT_EQUALS(total_len, aws_cbor_decoder_get_unconsumed_length(decoder));

    /* peek_type: old API (remaining_length) DOES decrease, new API (unconsumed_length) does NOT */
    enum aws_cbor_type out_type;
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_TRUE(aws_cbor_decoder_get_remaining_length(decoder) < total_len);
    ASSERT_UINT_EQUALS(total_len, aws_cbor_decoder_get_unconsumed_length(decoder));

    /* after pop, both decrease */
    uint64_t val;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &val));
    ASSERT_UINT_EQUALS(42, val);
    size_t after_first_pop = aws_cbor_decoder_get_unconsumed_length(decoder);
    ASSERT_TRUE(after_first_pop < total_len);
    ASSERT_UINT_EQUALS(after_first_pop, aws_cbor_decoder_get_remaining_length(decoder));

    /* peek second element: unconsumed_length unchanged, remaining_length decreases */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(after_first_pop, aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_TRUE(aws_cbor_decoder_get_remaining_length(decoder) < after_first_pop);

    /* pop second, both should be 0 */
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &val));
    ASSERT_UINT_EQUALS(100, val);
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_unconsumed_length(decoder));

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Encodes `input` (base-10 integer) and checks that the result is `expected_hex`, then decodes it back.
static int s_check_big_integer_cbor(struct aws_allocator *allocator, const char *input, const char *expected_hex) {
    struct aws_big_integer *value = aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str(input));
    ASSERT_NOT_NULL(value, "input: %s", input);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_big_integer(encoder, value);

    struct aws_byte_buf hex;
    ASSERT_SUCCESS(aws_byte_buf_init(&hex, allocator, 16));
    struct aws_byte_cursor encoded = aws_cbor_encoder_get_encoded_data(encoder);
    ASSERT_SUCCESS(aws_hex_encode_append_dynamic(&encoded, &hex));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&hex), expected_hex, "input: %s", input);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, encoded);
    struct aws_big_integer *decoded = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &decoded));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    struct aws_byte_buf str;
    ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 16));
    ASSERT_SUCCESS(aws_big_integer_to_str(decoded, &str));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), input, "input: %s", input);

    aws_byte_buf_clean_up(&str);
    aws_big_integer_destroy(decoded);
    aws_cbor_decoder_destroy(decoder);
    aws_byte_buf_clean_up(&hex);
    aws_cbor_encoder_destroy(encoder);
    aws_big_integer_destroy(value);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_big_integer_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    // The preferred serialization uses plain integers up to 64 bits, bignums beyond. See RFC8949 appendix A.
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "0", "00"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "23", "17"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "18446744073709551615", "1bffffffffffffffff"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "18446744073709551616", "c249010000000000000000"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-1", "20"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-100", "3863"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-18446744073709551616", "3bffffffffffffffff"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-18446744073709551617", "c349010000000000000000"));

    // 2^72 takes 10 bytes. The magnitude of -2^72 is 2^72 - 1, which takes 9.
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "4722366482869645213696", "c24a01000000000000000000"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-4722366482869645213696", "c349ffffffffffffffffff"));
    ASSERT_SUCCESS(s_check_big_integer_cbor(allocator, "-4722366482869645213697", "c34a01000000000000000000"));

    // The extremes allowed by aws_big_integer: 2^32768 - 1, and -(2^32768 - 1), whose magnitude is 2^32768 - 2.
    uint8_t max_bytes[4096];
    memset(max_bytes, 0xff, sizeof(max_bytes));
    struct aws_byte_cursor max_cursor = aws_byte_cursor_from_array(max_bytes, sizeof(max_bytes));
    struct aws_big_integer *max = aws_big_integer_new(allocator, max_cursor, false);
    ASSERT_NOT_NULL(max);
    struct aws_big_integer *neg_max = aws_big_integer_new(allocator, max_cursor, true);
    ASSERT_NOT_NULL(neg_max);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_big_integer(encoder, max);
    aws_cbor_encoder_write_big_integer(encoder, neg_max);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_cbor_encoder_get_encoded_data(encoder));

    struct aws_big_integer *decoded = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &decoded));
    struct aws_big_integer *expected = max;
    for (int i = 0; i < 2; ++i) {
        struct aws_byte_buf a;
        struct aws_byte_buf b;
        ASSERT_SUCCESS(aws_byte_buf_init(&a, allocator, 1));
        ASSERT_SUCCESS(aws_byte_buf_init(&b, allocator, 1));
        ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(expected, &a));
        ASSERT_SUCCESS(aws_big_integer_get_magnitude_be(decoded, &b));
        ASSERT_TRUE(aws_byte_buf_eq(&a, &b));
        ASSERT_INT_EQUALS(aws_big_integer_get_sign(expected), aws_big_integer_get_sign(decoded));
        aws_byte_buf_clean_up(&a);
        aws_byte_buf_clean_up(&b);
        aws_big_integer_destroy(decoded);
        decoded = NULL;
        expected = neg_max;
        if (i == 0) {
            ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &decoded));
        }
    }
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_decoder_destroy(decoder);
    aws_cbor_encoder_destroy(encoder);
    aws_big_integer_destroy(neg_max);
    aws_big_integer_destroy(max);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Decodes `hex` as one big integer and checks the base-10 value.
static int s_check_decode_big_integer(struct aws_allocator *allocator, const char *hex, const char *expected) {
    uint8_t data[64];
    struct aws_byte_buf buf = aws_byte_buf_from_empty_array(data, sizeof(data));
    struct aws_byte_cursor hex_cursor = aws_byte_cursor_from_c_str(hex);
    ASSERT_SUCCESS(aws_hex_decode(&hex_cursor, &buf), "hex: %s", hex);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_buf(&buf));
    struct aws_big_integer *value = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value), "hex: %s", hex);
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    struct aws_byte_buf str;
    ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 16));
    ASSERT_SUCCESS(aws_big_integer_to_str(value, &str));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), expected, "hex: %s", hex);

    aws_byte_buf_clean_up(&str);
    aws_big_integer_destroy(value);
    aws_cbor_decoder_destroy(decoder);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_big_integer_non_preferred_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    // Bignums for values that fit in 64 bits, and leading zero bytes, are valid.
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c240", "0"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c24105", "5"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c2420005", "5"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c24a000001000000000000ff", "72057594037928191"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c340", "-1"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c34100", "-1"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c34163", "-100"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "c348ffffffffffffffff", "-18446744073709551616"));
    // Plain integers of any width.
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "1b0000000000000001", "1"));
    ASSERT_SUCCESS(s_check_decode_big_integer(allocator, "3a00000000", "-1"));

    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_big_integer_errors_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    uint8_t data[4096 + 16];
    struct aws_big_integer *value = NULL;
    uint64_t u64 = 0;
    struct aws_byte_cursor cursor;
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_array(data, 0));

    // Not an integer. The decoder is left at the data item, so the right pop can be used.
    uint8_t text[] = {0x61, 'a'};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(text, sizeof(text)));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_NULL(value);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_text_val(decoder, &cursor));
    ASSERT_UINT_EQUALS(1, cursor.len);

    // A tag other than 2 and 3.
    uint8_t other_tag[] = {0xc1, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(other_tag, sizeof(other_tag)));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(other_tag), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_tag_val(decoder, &u64));
    ASSERT_UINT_EQUALS(1, u64);

    // A bignum tag not followed by a byte string.
    uint8_t not_bytes[] = {0xc2, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(not_bytes, sizeof(not_bytes)));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(not_bytes), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    // Indefinite-length byte strings are not supported.
    uint8_t indef[] = {0xc2, 0x5f, 0x41, 0x01, 0xff};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(indef, sizeof(indef)));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(indef), aws_cbor_decoder_get_unconsumed_length(decoder));

    // Truncated data is malformed and fails the decoder for good.
    uint8_t truncated[] = {0xc2, 0x49, 0x01, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(truncated, sizeof(truncated)));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());

    // Too long: 4097 bytes with a nonzero first byte. 4096 zero bytes are the value 0.
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    memset(data, 0, sizeof(data));
    data[0] = 0x01;
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_UNSIGNED_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(data, 4097));
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_UNSIGNED_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(data + 1, 4096));
    aws_cbor_decoder_reset_src(decoder, aws_cbor_encoder_get_encoded_data(encoder));
    size_t total = aws_cbor_decoder_get_remaining_length(decoder);
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_ARGUMENT, aws_last_error());
    ASSERT_UINT_EQUALS(total, aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_INT_EQUALS(0, aws_big_integer_get_sign(value));
    aws_big_integer_destroy(value);
    value = NULL;

    // -1 - (2^32768 - 1) is -2^32768, outside the limits.
    aws_cbor_encoder_reset(encoder);
    memset(data, 0xff, 4096);
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_NEGATIVE_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(data, 4096));
    aws_cbor_decoder_reset_src(decoder, aws_cbor_encoder_get_encoded_data(encoder));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_ARGUMENT, aws_last_error());
    ASSERT_NULL(value);

    // A negative bignum of more than 4096 bytes is rejected without regard to its value, and the decoder is restored.
    aws_cbor_encoder_reset(encoder);
    memset(data, 0, sizeof(data));
    data[0] = 0x01;
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_NEGATIVE_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(data, 4097));
    aws_cbor_decoder_reset_src(decoder, aws_cbor_encoder_get_encoded_data(encoder));
    total = aws_cbor_decoder_get_remaining_length(decoder);
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_ARGUMENT, aws_last_error());
    ASSERT_NULL(value);
    ASSERT_UINT_EQUALS(total, aws_cbor_decoder_get_unconsumed_length(decoder));

    // Leading zeros don't count towards the size: 4097 zero bytes are n = 0, which is -1.
    aws_cbor_encoder_reset(encoder);
    memset(data, 0, sizeof(data));
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_NEGATIVE_BIGNUM);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(data, 4097));
    aws_cbor_decoder_reset_src(decoder, aws_cbor_encoder_get_encoded_data(encoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &value));
    ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(value));
    struct aws_byte_buf minus_one;
    ASSERT_SUCCESS(aws_byte_buf_init(&minus_one, allocator, 2));
    ASSERT_SUCCESS(aws_big_integer_to_str(value, &minus_one));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&minus_one), "-1");
    aws_byte_buf_clean_up(&minus_one);
    aws_big_integer_destroy(value);
    value = NULL;

    aws_cbor_encoder_destroy(encoder);
    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Encodes `input` (as accepted by aws_big_decimal_new_from_cursor) and checks that the result is `expected_hex`, then
// decodes it back and checks for an identical value.
static int s_check_big_decimal_cbor(
    struct aws_allocator *allocator,
    const char *input,
    const char *expected_hex,
    const char *expected_str) {

    struct aws_big_decimal *value = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str(input));
    ASSERT_NOT_NULL(value, "input: %s", input);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_big_decimal(encoder, value);

    struct aws_byte_buf hex;
    ASSERT_SUCCESS(aws_byte_buf_init(&hex, allocator, 16));
    struct aws_byte_cursor encoded = aws_cbor_encoder_get_encoded_data(encoder);
    ASSERT_SUCCESS(aws_hex_encode_append_dynamic(&encoded, &hex));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&hex), expected_hex, "input: %s", input);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, encoded);
    struct aws_big_decimal *decoded = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decoded));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));
    ASSERT_INT_EQUALS(aws_big_decimal_get_exponent(value), aws_big_decimal_get_exponent(decoded));

    struct aws_byte_buf str;
    ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 16));
    ASSERT_SUCCESS(aws_big_decimal_to_str(decoded, &str));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), expected_str, "input: %s", input);

    aws_byte_buf_clean_up(&str);
    aws_big_decimal_destroy(decoded);
    aws_cbor_decoder_destroy(decoder);
    aws_byte_buf_clean_up(&hex);
    aws_cbor_encoder_destroy(encoder);
    aws_big_decimal_destroy(value);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_big_decimal_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    // 273.15 is the example in RFC8949 section 3.4.4
    ASSERT_SUCCESS(s_check_big_decimal_cbor(allocator, "273.15", "c48221196ab3", "27315e-2"));
    // The scale is preserved
    ASSERT_SUCCESS(s_check_big_decimal_cbor(allocator, "1.50", "c482211896", "150e-2"));
    ASSERT_SUCCESS(s_check_big_decimal_cbor(allocator, "15e-1", "c482200f", "15e-1"));
    ASSERT_SUCCESS(s_check_big_decimal_cbor(allocator, "0e0", "c4820000", "0e0"));
    ASSERT_SUCCESS(s_check_big_decimal_cbor(allocator, "-5e3", "c4820324", "-5e3"));
    // Bignum mantissas
    ASSERT_SUCCESS(s_check_big_decimal_cbor(
        allocator, "18446744073709551616e1", "c48201c249010000000000000000", "18446744073709551616e1"));
    ASSERT_SUCCESS(s_check_big_decimal_cbor(
        allocator, "-18446744073709551617e-1", "c48220c349010000000000000000", "-18446744073709551617e-1"));
    // The limits of the exponent
    ASSERT_SUCCESS(s_check_big_decimal_cbor(
        allocator, "1e9223372036854775807", "c4821b7fffffffffffffff01", "1e9223372036854775807"));
    ASSERT_SUCCESS(s_check_big_decimal_cbor(
        allocator, "1e-9223372036854775808", "c4823b7fffffffffffffff01", "1e-9223372036854775808"));

    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Decodes `hex`, which must be a single decimal fraction followed by the unsigned integer 5.
static int s_check_decode_big_decimal(struct aws_allocator *allocator, const char *hex, const char *expected_str) {
    uint8_t data[64];
    struct aws_byte_buf buf = aws_byte_buf_from_empty_array(data, sizeof(data));
    struct aws_byte_cursor hex_cursor = aws_byte_cursor_from_c_str(hex);
    ASSERT_SUCCESS(aws_hex_decode(&hex_cursor, &buf), "hex: %s", hex);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_buf(&buf));
    struct aws_big_decimal *value = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &value), "hex: %s", hex);

    struct aws_byte_buf str;
    ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 16));
    ASSERT_SUCCESS(aws_big_decimal_to_str(value, &str));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), expected_str, "hex: %s", hex);

    uint64_t next = 0;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &next), "hex: %s", hex);
    ASSERT_UINT_EQUALS(5, next, "hex: %s", hex);
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_byte_buf_clean_up(&str);
    aws_big_decimal_destroy(value);
    aws_cbor_decoder_destroy(decoder);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_big_decimal_indefinite_array_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    ASSERT_SUCCESS(s_check_decode_big_decimal(allocator, "c48221196ab305", "27315e-2"));
    ASSERT_SUCCESS(s_check_decode_big_decimal(allocator, "c49f21196ab3ff05", "27315e-2"));
    ASSERT_SUCCESS(s_check_decode_big_decimal(allocator, "c49f0000ff05", "0e0"));
    ASSERT_SUCCESS(s_check_decode_big_decimal(allocator, "c49f01c249010000000000000000ff05", "18446744073709551616e1"));
    ASSERT_SUCCESS(
        s_check_decode_big_decimal(allocator, "c49f20c349010000000000000000ff05", "-18446744073709551617e-1"));

    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

static int s_check_decode_big_decimal_fails(
    struct aws_allocator *allocator,
    const char *hex,
    int expected_error,
    size_t expected_unconsumed) {

    uint8_t data[64];
    struct aws_byte_buf buf = aws_byte_buf_from_empty_array(data, sizeof(data));
    struct aws_byte_cursor hex_cursor = aws_byte_cursor_from_c_str(hex);
    ASSERT_SUCCESS(aws_hex_decode(&hex_cursor, &buf), "hex: %s", hex);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_buf(&buf));
    struct aws_big_decimal *value = NULL;
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &value), "hex: %s", hex);
    ASSERT_INT_EQUALS(expected_error, aws_last_error(), "hex: %s", hex);
    ASSERT_NULL(value);
    ASSERT_UINT_EQUALS(expected_unconsumed, aws_cbor_decoder_get_unconsumed_length(decoder), "hex: %s", hex);

    aws_cbor_decoder_destroy(decoder);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_big_decimal_errors_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    // Each of these leaves the decoder at the start of the data item.
    // Not a tag
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "820000", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 3));
    // A different tag
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c5820000", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 4));
    // Tag not followed by an array
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c400", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 2));
    // Wrong number of elements
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c48100", AWS_ERROR_INVALID_CBOR, 3));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c483000000", AWS_ERROR_INVALID_CBOR, 5));
    // Wrong number of elements in an indefinite-length array: none, one, three, and a missing break
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49fff", AWS_ERROR_INVALID_CBOR, 3));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49f00ff", AWS_ERROR_INVALID_CBOR, 4));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49f000000ff", AWS_ERROR_INVALID_CBOR, 6));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49f0000", AWS_ERROR_INVALID_CBOR, 4));
    // Indefinite-length array with a bad exponent or mantissa
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49f616100ff", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49f006161ff", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    // Exponent that is not an integer: text, float, bignum
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482616100", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 5));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482f93c0000", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482c2410100", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482c3410100", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c49fc2410100ff", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 7));
    // Exponent outside int64_t: 2^63, and -1 - 2^63
    ASSERT_SUCCESS(
        s_check_decode_big_decimal_fails(allocator, "c4821b800000000000000000", AWS_ERROR_OVERFLOW_DETECTED, 12));
    ASSERT_SUCCESS(
        s_check_decode_big_decimal_fails(allocator, "c4823b800000000000000000", AWS_ERROR_OVERFLOW_DETECTED, 12));
    // Mantissa that is not an integer
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482006161", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 5));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c48200f93c00", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 6));
    // Mantissa that is a bignum tag not followed by bytes
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c48200c200", AWS_ERROR_CBOR_UNEXPECTED_TYPE, 5));
    // Missing mantissa
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c48200", AWS_ERROR_INVALID_CBOR, 3));
    // Truncated after the tag, and after the array header
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c4", AWS_ERROR_INVALID_CBOR, 1));
    ASSERT_SUCCESS(s_check_decode_big_decimal_fails(allocator, "c482", AWS_ERROR_INVALID_CBOR, 2));

    // Decimals in a sequence, and a decode that fails leaves the next data item readable.
    uint8_t data[] = {0xc4, 0x82, 0x21, 0x19, 0x6a, 0xb3, 0xc4, 0x82, 0x00, 0x61, 0x61, 0x05};
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_array(data, sizeof(data)));
    struct aws_big_decimal *value = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &value));
    ASSERT_INT_EQUALS(-2, aws_big_decimal_get_exponent(value));
    aws_big_decimal_destroy(value);
    value = NULL;
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &value));
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    uint64_t u64 = 0;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(5, u64);
    aws_cbor_decoder_destroy(decoder);

    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Decodes a decimal fraction whose mantissa is a bignum of 4097 bytes, the first of which is nonzero.
static int s_check_oversized_decimal_mantissa(struct aws_allocator *allocator, uint64_t mantissa_tag) {
    uint8_t mantissa[4097] = {0x01};

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_tag(encoder, AWS_CBOR_TAG_DECIMAL_FRACTION);
    aws_cbor_encoder_write_array_start(encoder, 2);
    aws_cbor_encoder_write_uint(encoder, 3);
    aws_cbor_encoder_write_tag(encoder, mantissa_tag);
    aws_cbor_encoder_write_bytes(encoder, aws_byte_cursor_from_array(mantissa, sizeof(mantissa)));
    aws_cbor_encoder_write_uint(encoder, 9);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_cbor_encoder_get_encoded_data(encoder));
    size_t total = aws_cbor_decoder_get_remaining_length(decoder);

    struct aws_big_decimal *value = NULL;
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &value));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_ARGUMENT, aws_last_error());
    ASSERT_NULL(value);
    ASSERT_UINT_EQUALS(total, aws_cbor_decoder_get_unconsumed_length(decoder));

    // The decoder is intact, so the whole item can be skipped and the next one read.
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    uint64_t next = 0;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &next));
    ASSERT_UINT_EQUALS(9, next);

    aws_cbor_decoder_destroy(decoder);
    aws_cbor_encoder_destroy(encoder);
    return AWS_OP_SUCCESS;
}

CBOR_TEST_CASE(cbor_decode_big_decimal_oversized_mantissa_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    ASSERT_SUCCESS(s_check_oversized_decimal_mantissa(allocator, AWS_CBOR_TAG_UNSIGNED_BIGNUM));
    ASSERT_SUCCESS(s_check_oversized_decimal_mantissa(allocator, AWS_CBOR_TAG_NEGATIVE_BIGNUM));

    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// The big number pops are often called after the caller peeked the type. A failure must leave that peeked data item
// available to a different pop, and a success must consume it.
CBOR_TEST_CASE(cbor_decode_big_after_peek_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, aws_byte_cursor_from_array(NULL, 0));
    enum aws_cbor_type type;
    uint64_t u64 = 0;
    struct aws_byte_cursor cursor;
    struct aws_big_integer *integer = NULL;
    struct aws_big_decimal *decimal = NULL;

    // Peeked tag that isn't a bignum
    uint8_t other_tag[] = {0xc1, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(other_tag, sizeof(other_tag)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_INT_EQUALS(AWS_CBOR_TYPE_TAG, type);
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &integer));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(other_tag), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_tag_val(decoder, &u64));
    ASSERT_UINT_EQUALS(1, u64);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(0, u64);

    // Peeked text
    uint8_t text[] = {0x61, 'a'};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(text, sizeof(text)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &integer));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decimal));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(text), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_text_val(decoder, &cursor));
    ASSERT_UINT_EQUALS(1, cursor.len);

    // Peeked bignum tag whose byte string is missing: the tag is not consumed
    uint8_t not_bytes[] = {0xc2, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(not_bytes, sizeof(not_bytes)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &integer));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(not_bytes), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_tag_val(decoder, &u64));
    ASSERT_UINT_EQUALS(AWS_CBOR_TAG_UNSIGNED_BIGNUM, u64);

    // Peeked integer that isn't a decimal fraction
    uint8_t uint_val[] = {0x05};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(uint_val, sizeof(uint_val)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decimal));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(uint_val), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(5, u64);

    // Peeked tag that isn't a decimal fraction
    uint8_t wrong_decimal_tag[] = {0xc5, 0x82, 0x00, 0x00};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(wrong_decimal_tag, sizeof(wrong_decimal_tag)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_FAILS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decimal));
    ASSERT_UINT_EQUALS(AWS_ERROR_CBOR_UNEXPECTED_TYPE, aws_last_error());
    ASSERT_UINT_EQUALS(sizeof(wrong_decimal_tag), aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_tag_val(decoder, &u64));
    ASSERT_UINT_EQUALS(5, u64);

    // Successes after a peek consume the peeked item along with the rest
    uint8_t bignum[] = {0xc2, 0x41, 0x05, 0x07};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(bignum, sizeof(bignum)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &integer));
    ASSERT_INT_EQUALS(1, aws_big_integer_get_sign(integer));
    aws_big_integer_destroy(integer);
    integer = NULL;
    ASSERT_UINT_EQUALS(1, aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(7, u64);

    uint8_t small_int[] = {0x20, 0x07};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(small_int, sizeof(small_int)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &integer));
    ASSERT_INT_EQUALS(-1, aws_big_integer_get_sign(integer));
    aws_big_integer_destroy(integer);
    integer = NULL;
    ASSERT_UINT_EQUALS(1, aws_cbor_decoder_get_unconsumed_length(decoder));

    uint8_t decimal_item[] = {0xc4, 0x82, 0x21, 0x18, 0x96, 0x07};
    aws_cbor_decoder_reset_src(decoder, aws_byte_cursor_from_array(decimal_item, sizeof(decimal_item)));
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &type));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decimal));
    ASSERT_INT_EQUALS(-2, aws_big_decimal_get_exponent(decimal));
    aws_big_decimal_destroy(decimal);
    decimal = NULL;
    ASSERT_UINT_EQUALS(1, aws_cbor_decoder_get_unconsumed_length(decoder));
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(7, u64);

    aws_cbor_decoder_destroy(decoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}

// Big numbers written between other data items, inside a container.
CBOR_TEST_CASE(cbor_encode_decode_big_in_container_test) {
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_big_integer *positive =
        aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("18446744073709551616"));
    ASSERT_NOT_NULL(positive);
    struct aws_big_integer *negative =
        aws_big_integer_new_from_cursor(allocator, aws_byte_cursor_from_c_str("-18446744073709551617"));
    ASSERT_NOT_NULL(negative);
    struct aws_big_decimal *decimal = aws_big_decimal_new_from_cursor(allocator, aws_byte_cursor_from_c_str("1.50"));
    ASSERT_NOT_NULL(decimal);

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    aws_cbor_encoder_write_array_start(encoder, 4);
    aws_cbor_encoder_write_big_integer(encoder, positive);
    aws_cbor_encoder_write_big_integer(encoder, negative);
    aws_cbor_encoder_write_big_decimal(encoder, decimal);
    aws_cbor_encoder_write_uint(encoder, 7);

    struct aws_byte_buf hex;
    ASSERT_SUCCESS(aws_byte_buf_init(&hex, allocator, 16));
    struct aws_byte_cursor encoded = aws_cbor_encoder_get_encoded_data(encoder);
    ASSERT_SUCCESS(aws_hex_encode_append_dynamic(&encoded, &hex));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(
        aws_byte_cursor_from_buf(&hex), "84c249010000000000000000c349010000000000000000c48221189607");

    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, encoded);
    uint64_t u64 = 0;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_array_start(decoder, &u64));
    ASSERT_UINT_EQUALS(4, u64);

    struct aws_big_integer *decoded_integer = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &decoded_integer));
    ASSERT_TRUE(aws_big_integer_eq(positive, decoded_integer));
    aws_big_integer_destroy(decoded_integer);

    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_integer_val(decoder, &decoded_integer));
    ASSERT_TRUE(aws_big_integer_eq(negative, decoded_integer));
    aws_big_integer_destroy(decoded_integer);

    struct aws_big_decimal *decoded_decimal = NULL;
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_big_decimal_val(decoder, &decoded_decimal));
    ASSERT_INT_EQUALS(-2, aws_big_decimal_get_exponent(decoded_decimal));
    struct aws_byte_buf str;
    ASSERT_SUCCESS(aws_byte_buf_init(&str, allocator, 16));
    ASSERT_SUCCESS(aws_big_decimal_to_str(decoded_decimal, &str));
    ASSERT_CURSOR_VALUE_CSTRING_EQUALS(aws_byte_cursor_from_buf(&str), "150e-2");
    aws_byte_buf_clean_up(&str);
    aws_big_decimal_destroy(decoded_decimal);

    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &u64));
    ASSERT_UINT_EQUALS(7, u64);
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_decoder_destroy(decoder);
    aws_byte_buf_clean_up(&hex);
    aws_cbor_encoder_destroy(encoder);
    aws_big_decimal_destroy(decimal);
    aws_big_integer_destroy(negative);
    aws_big_integer_destroy(positive);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}
