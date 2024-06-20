/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cbor.h>
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
    enum { VALUE_NUM = 10 };

    /**
     * 1 as unsigned int, takes 1 byte
     * -1 as negative int, takes 1 byte
     * 1.1 double, takes 9 bytes
     * 1.1f is float, takes 5 bytes
     * -1.1f is float, takes 5 bytes
     * INFINITY will be float, takes 5 bytes
     * FLT_MAX still a float, take 5 bytes
     * DBL_MAX will be a double takes 9 bytes
     * DBL_MIN will be a double takes 9 bytes
     * HUGE_VAL
     */
    double values[VALUE_NUM] = {1.0, -1.0, 1.1, 1.1f, -1.1f, INFINITY, FLT_MAX, DBL_MAX, DBL_MIN, HUGE_VAL};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 1, 9, 5, 5, 5, 5, 9, 9, 5};

    int expected_encoded_type[VALUE_NUM] = {
        AWS_CBOR_TYPE_UINT,
        AWS_CBOR_TYPE_NEGINT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
        AWS_CBOR_TYPE_FLOAT,
    };

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encoder_write_float(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, final_cursor);
    /* Unsigned int, 1 */
    size_t index = 0;
    uint64_t result = 0;
    enum aws_cbor_type out_type = AWS_CBOR_TYPE_UNKNOWN;
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_unsigned_int_val(decoder, &result));
    ASSERT_TRUE(values[index++] == result);
    /* negative int, -1 */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_negative_int_val(decoder, &result));
    /* Convert the decode val to expected val. */
    ASSERT_TRUE((-1 - values[index++]) == result);
    /* 1.1 double */
    double double_result = 0;
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* 1.1 float */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* -1.1 float */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* INFINITY */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* FLT_MAX */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* DBL_MAX */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* DBL_MIN */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* HUGE_VAL */
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decoder_pop_next_float_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);

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
    aws_cbor_decoder_pop_next_array_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, UINT16_MAX + 1);
    aws_cbor_decoder_pop_next_map_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, UINT16_MAX + 1);

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
    aws_cbor_decoder_destroy(decoder);

    /* 2. Empty cursor */
    struct aws_byte_cursor empty = {0};
    decoder = aws_cbor_decoder_new(allocator, empty);
    ASSERT_FAILS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_ERROR_INVALID_CBOR, aws_last_error());
    aws_cbor_decoder_destroy(decoder);

    /* 3. Try get wrong type */
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator);
    uint64_t val = 1;
    aws_cbor_encoder_write_uint(encoder, val);
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    decoder = aws_cbor_decoder_new(allocator, final_cursor);
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
    aws_cbor_decoder_destroy(decoder);

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
    decoder = aws_cbor_decoder_new(allocator, final_cursor);
    ASSERT_SUCCESS(aws_cbor_decoder_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(AWS_CBOR_TYPE_MAP_START, out_type);
    ASSERT_SUCCESS(aws_cbor_decoder_consume_next_whole_data_item(decoder));
    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));
    aws_cbor_decoder_destroy(decoder);

    aws_cbor_encoder_destroy(encoder);
    aws_common_library_clean_up();
    return AWS_OP_SUCCESS;
}
