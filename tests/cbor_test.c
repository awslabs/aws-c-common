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
    enum { VALUE_NUM = 5 };

    /**
     * Less than 24 only take 1 byte,
     * 24 to uint8_t max takes 2 bytes
     * uint8_t max to uint16_t max takes 3 bytes
     * uint16_t max to uint32_t maxx takes 5 bytes
     * uint32_t max to uint64_t max takes 9 bytes
     */
    uint64_t values[VALUE_NUM] = {23, 24, UINT8_MAX + 1, UINT16_MAX + 1U, UINT32_MAX + 1LLU};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 2, 3, 5, 9};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);
    /* Unsigned int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_uint(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    /* Negative int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_negint(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);
    /* Unsigned int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        uint64_t result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_unsigned_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }
    /* Negative int */
    for (size_t i = 0; i < VALUE_NUM; i++) {
        uint64_t result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_neg_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_double_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    enum { VALUE_NUM = 6 };

    /**
     * 1 as unsigned int, takes 1 byte
     * -1 as negative int, takes 1 byte
     * 1.1 will be double, takes 5 bytes TODO: (double)1.1 turns to 1.1000000000000001 on Mac, thus it will be convert
     * to double
     * INFINITY will be float, takes 5 bytes
     * FLT_MAX still a float, take 5 bytes
     * DBL_MAX will be a double
     * takes 9 bytes
     */
    double values[VALUE_NUM] = {1.0, -1.0, 1.1, INFINITY, FLT_MAX, DBL_MAX};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 1, 9, 5, 5, 9};

    int expected_encoded_type[VALUE_NUM] = {
        AWS_CBOR_TYPE_UINT,
        AWS_CBOR_TYPE_NEGINT,
        AWS_CBOR_TYPE_DOUBLE,
        AWS_CBOR_TYPE_DOUBLE,
        AWS_CBOR_TYPE_DOUBLE,
        AWS_CBOR_TYPE_DOUBLE,
    };

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_double(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);
    /* Unsigned int, 1 */
    size_t index = 0;
    uint64_t result = 0;
    enum aws_cbor_element_type out_type = AWS_CBOR_TYPE_MAX;
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_unsigned_val(decoder, &result));
    ASSERT_TRUE(values[index++] == result);
    /* negative int, -1 */
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_neg_val(decoder, &result));
    /* Convert negative val to unsigned for easier comparing. */
    ASSERT_TRUE((-1 * values[index++]) == result);
    /* 1.1 */
    double double_result = 0;
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_double_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* INFINITY */
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_double_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* FLT_MAX */
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_double_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);
    /* DBL_MAX */
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, expected_encoded_type[index]);
    ASSERT_SUCCESS(aws_cbor_decode_get_next_double_val(decoder, &double_result));
    ASSERT_TRUE(values[index++] == double_result);

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_bool_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    enum { VALUE_NUM = 2 };
    bool values[VALUE_NUM] = {true, false};
    uint64_t expected_encoded_len[VALUE_NUM] = {1, 1};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_bool(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        bool result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_boolean_val(decoder, &result));
        ASSERT_UINT_EQUALS(values[i], result);
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_bytesstr_str_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    enum { VALUE_NUM = 2 };
    struct aws_byte_cursor *values[VALUE_NUM] = {&val_1, &val_2};
    uint64_t expected_encoded_len[VALUE_NUM] = {1 + val_1.len, 1 + val_2.len};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_string(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_bytes(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }
    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_str_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, values[i]));
    }
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_bytes_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, values[i]));
    }

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_array_map_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    enum { VALUE_NUM = 2 };
    struct aws_byte_cursor *values[VALUE_NUM] = {&val_1, &val_2};
    uint64_t expected_encoded_len[VALUE_NUM] = {1 + val_1.len, 1 + val_2.len};

    size_t encoded_len = 0;
    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);

    /* Array with 2 elements */
    aws_cbor_encode_array_start(encoder, 2);
    struct aws_byte_cursor encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* Array start with 2 element only takes 1 byte */
    ASSERT_UINT_EQUALS(encoded_len + 1, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_string(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }

    /* Map with 1 element */
    aws_cbor_encode_map_start(encoder, 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* Map start with 1 (key, value pair) only takes 1 byte */
    ASSERT_UINT_EQUALS(encoded_len + 1, encoded_cursor.len);
    encoded_len = encoded_cursor.len;
    for (size_t i = 0; i < VALUE_NUM; i++) {
        aws_cbor_encode_bytes(encoder, values[i]);
        struct aws_byte_cursor cursor = aws_cbor_encoder_get_encoded_data(encoder);
        ASSERT_UINT_EQUALS(encoded_len + expected_encoded_len[i], cursor.len);
        encoded_len = cursor.len;
    }

    /* Map with a lot element, not closure. */
    aws_cbor_encode_array_start(encoder, UINT16_MAX + 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* The size takes 4 bytes and one more for the cbor start item */
    ASSERT_UINT_EQUALS(encoded_len + 5, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    aws_cbor_encode_map_start(encoder, UINT16_MAX + 1);
    encoded_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    /* The size takes 4 bytes and one more for the cbor start item */
    ASSERT_UINT_EQUALS(encoded_len + 5, encoded_cursor.len);
    encoded_len = encoded_cursor.len;

    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);

    uint64_t element_size = 0;
    aws_cbor_decode_get_next_array_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, 2);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_str_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, values[i]));
    }
    aws_cbor_decode_get_next_map_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, 1);
    for (size_t i = 0; i < VALUE_NUM; i++) {
        struct aws_byte_cursor result;
        ASSERT_SUCCESS(aws_cbor_decode_get_next_bytes_val(decoder, &result));
        ASSERT_TRUE(aws_byte_cursor_eq(&result, values[i]));
    }
    aws_cbor_decode_get_next_array_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, UINT16_MAX + 1);
    aws_cbor_decode_get_next_map_start(decoder, &element_size);
    ASSERT_UINT_EQUALS(element_size, UINT16_MAX + 1);

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}

CBOR_TEST_CASE(cbor_encode_decode_inf_test) {
    (void)allocator;
    (void)ctx;
    aws_common_library_init(allocator);
    struct aws_byte_cursor val_1 = aws_byte_cursor_from_c_str("my test");
    struct aws_byte_cursor val_2 = aws_byte_cursor_from_c_str("write more tests");

    struct aws_cbor_encoder *encoder = aws_cbor_encoder_new(allocator, 128);

    /* Create a non-sense stack of inf collections. */
    aws_cbor_encode_inf_start(encoder, AWS_CBOR_TYPE_INF_MAP_START);
    /* Key */
    aws_cbor_encode_string(encoder, &val_1);
    /* Value */
    aws_cbor_encode_inf_start(encoder, AWS_CBOR_TYPE_INF_ARRAY_START);
    /* element 1 in array */
    aws_cbor_encode_inf_start(encoder, AWS_CBOR_TYPE_INF_STRING);
    aws_cbor_encode_string(encoder, &val_1);
    aws_cbor_encode_string(encoder, &val_2);
    aws_cbor_encode_break(encoder);
    /* element 2 in array */
    aws_cbor_encode_inf_start(encoder, AWS_CBOR_TYPE_INF_BYTESTRING);
    aws_cbor_encode_bytes(encoder, &val_1);
    aws_cbor_encode_bytes(encoder, &val_2);
    aws_cbor_encode_break(encoder);
    /* Closure for the array */
    aws_cbor_encode_break(encoder);
    /* Closure for the map */
    aws_cbor_encode_break(encoder);

    struct aws_byte_cursor final_cursor = aws_cbor_encoder_get_encoded_data(encoder);
    struct aws_cbor_decoder *decoder = aws_cbor_decoder_new(allocator, &final_cursor);

    enum aws_cbor_element_type out_type = AWS_CBOR_TYPE_MAX;
    ASSERT_SUCCESS(aws_cbor_decode_peek_type(decoder, &out_type));
    ASSERT_UINT_EQUALS(out_type, AWS_CBOR_TYPE_INF_MAP_START);

    /* Get rid of the whole inf map with all the data content */
    ASSERT_SUCCESS(aws_cbor_decode_consume_next_data_item(decoder));

    ASSERT_UINT_EQUALS(0, aws_cbor_decoder_get_remaining_length(decoder));

    aws_cbor_encoder_release(encoder);
    aws_cbor_decoder_release(decoder);
    aws_common_library_clean_up();
    return SUCCESS;
}
