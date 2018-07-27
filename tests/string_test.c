/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/string.h>
#include <aws/common/hash_table.h>
#include <aws/testing/aws_test_harness.h>

AWS_TEST_CASE(string_tests, string_tests_fn);
static int string_tests_fn(struct aws_allocator *alloc, void *ctx) {
    /* Test: static string creation from macro works. */
    AWS_STATIC_STRING_FROM_LITERAL(test_string_1, "foofaraw");
    ASSERT_NULL(test_string_1->allocator, "Static string should have no allocator.");
    ASSERT_INT_EQUALS(test_string_1->len, 8, "Length should have been set correctly.");
    ASSERT_BIN_ARRAYS_EQUALS(aws_string_bytes(test_string_1), test_string_1->len, "foofaraw", 8,
                             "Data bytes should have been set correctly.");
    ASSERT_INT_EQUALS(aws_string_bytes(test_string_1)[test_string_1->len], '\0',
                      "Static string should have null byte at end.");

    /* Test: string creation works. */
    const struct aws_string *test_string_2 = aws_string_from_c_str_new(alloc, "foofaraw");
    ASSERT_NOT_NULL(test_string_2, "Memory allocation of string should have succeeded.");
    ASSERT_PTR_EQUALS(test_string_2->allocator, alloc, "Allocator should have been set correctly.");
    ASSERT_INT_EQUALS(test_string_2->len, 8, "Length should have been set correctly.");
    ASSERT_BIN_ARRAYS_EQUALS(aws_string_bytes(test_string_2), test_string_2->len, "foofaraw", 8,
                             "Data bytes should have been set correctly.");
    ASSERT_INT_EQUALS(aws_string_bytes(test_string_2)[test_string_2->len], '\0',
                      "String from C-string should have null byte at end.");

    /* Test: strings from first two tests are equal and have same hashes. */
    ASSERT_TRUE(aws_string_eq(test_string_1, test_string_2), "Buffers should be equal.");
    ASSERT_INT_EQUALS(aws_hash_string(test_string_1), aws_hash_string(test_string_2),
                      "Hash values of byte buffers should be equal.");

    /* Test: write from string to byte cursor works. */
    uint8_t dest[8] = {0};
    struct aws_byte_cursor dest_cur = aws_byte_cursor_from_array(dest, 8);

    ASSERT_TRUE(aws_byte_cursor_write_from_whole_string(&dest_cur, test_string_2),
                "Write from whole string should have succeeded.");
    ASSERT_BIN_ARRAYS_EQUALS(dest, 8, "foofaraw", 8);

    /* Test: write from string fails cleanly when byte cursor too short. */
    int8_t short_dest[7] = {0};
    struct aws_byte_cursor short_dest_cur = aws_byte_cursor_from_array(short_dest, 7);

    ASSERT_FALSE(aws_byte_cursor_write_from_whole_string(&short_dest_cur, test_string_2),
                 "Write from whole buffer should have failed.");
    ASSERT_INT_EQUALS(short_dest_cur.len, 7, "Destination cursor length should be unchanged.");
    ASSERT_INT_EQUALS(0, short_dest_cur.ptr[0], "Destination cursor should not have received data.");

    /* Test: all allocated memory is deallocated properly. */
    aws_string_destroy((void *)test_string_2);

    return 0;
}

AWS_TEST_CASE(binary_string_test, binary_string_test_fn);
static int binary_string_test_fn(struct aws_allocator *alloc, void *ctx) {
    uint8_t test_array[] = {0x86, 0x75, 0x30, 0x90, 0x00, 0xde, 0xad, 0xbe, 0xef};
    size_t len = sizeof(test_array);
    const struct aws_string *binary_string = aws_string_from_array_new(alloc, test_array, len);

    ASSERT_NOT_NULL(binary_string, "Memory allocation of string should have succeeded.");
    ASSERT_PTR_EQUALS(alloc, binary_string->allocator, "Allocator should have been set correctly.");
    ASSERT_BIN_ARRAYS_EQUALS(test_array, len, aws_string_bytes(binary_string), binary_string->len,
                             "Binary string bytes should be same as source array.");
    ASSERT_INT_EQUALS(aws_string_bytes(binary_string)[binary_string->len], 0x00,
                      "String from binary array should have null byte at end");
    aws_string_destroy((void *)binary_string);
    return 0;
}

AWS_TEST_CASE(string_compare_test, string_compare_test_fn);
static int string_compare_test_fn(struct aws_allocator *alloc, void *ctx) {
    AWS_STATIC_STRING_FROM_LITERAL(empty, "");
    AWS_STATIC_STRING_FROM_LITERAL(foo, "foo");
    AWS_STATIC_STRING_FROM_LITERAL(bar, "bar");
    AWS_STATIC_STRING_FROM_LITERAL(foobar, "foobar");
    AWS_STATIC_STRING_FROM_LITERAL(foo2, "foo");
    AWS_STATIC_STRING_FROM_LITERAL(foobaz, "foobaz");
    AWS_STATIC_STRING_FROM_LITERAL(bar_food, "bar food");
    AWS_STATIC_STRING_FROM_LITERAL(bar_null_food, "bar\0food");
    AWS_STATIC_STRING_FROM_LITERAL(bar_null_back, "bar\0back");

    ASSERT_TRUE(aws_string_compare(empty, bar) < 0);
    ASSERT_TRUE(aws_string_compare(foo, bar) > 0);
    ASSERT_TRUE(aws_string_compare(bar, foo) < 0);
    ASSERT_TRUE(aws_string_compare(foo, foobar) < 0);
    ASSERT_TRUE(aws_string_compare(foo, foo2) == 0);
    ASSERT_TRUE(aws_string_compare(foobar, foobaz) < 0);
    ASSERT_TRUE(aws_string_compare(foobaz, empty) > 0);
    ASSERT_TRUE(aws_string_compare(empty, empty) == 0);
    ASSERT_TRUE(aws_string_compare(foo, bar_food) > 0);
    ASSERT_TRUE(aws_string_compare(bar_food, bar) > 0);
    ASSERT_TRUE(aws_string_compare(bar_null_food, bar) > 0);
    ASSERT_TRUE(aws_string_compare(bar_null_food, bar_food) < 0);
    ASSERT_TRUE(aws_string_compare(bar_null_food, bar_null_back) > 0);

    /* Test that bytes are being compared as unsigned integers. */
    AWS_STATIC_STRING_FROM_LITERAL(x80, "\x80");
    AWS_STATIC_STRING_FROM_LITERAL(x7f, "\x79");
    ASSERT_TRUE(aws_string_compare(x80, x7f) > 0);
    ASSERT_TRUE(aws_string_compare(x7f, x80) < 0);
    return 0;
}

AWS_TEST_CASE(string_secure_destroy_test, string_secure_destroy_test_fn);
static int string_secure_destroy_test_fn(struct aws_allocator *alloc, void *ctx) {
    /* Just verifies all memory was freed. */
    const struct aws_string *empty = aws_string_from_c_str_new(alloc, "");
    const struct aws_string *logorrhea = aws_string_from_c_str_new(alloc, "logorrhea");
    const uint8_t bytes[] = {0xde, 0xad, 0xbe, 0xef, 0x00, 0x86, 0x75, 0x30, 0x90};
    const struct aws_string *deadbeef = aws_string_from_array_new(alloc, bytes, sizeof(bytes));
    ASSERT_NOT_NULL(empty, "Memory allocation of string should have succeeded.");
    ASSERT_NOT_NULL(logorrhea, "Memory allocation of string should have succeeded.");
    ASSERT_NOT_NULL(deadbeef, "Memory allocation of string should have succeeded.");
    aws_string_secure_destroy((void *)empty);
    aws_string_secure_destroy((void *)logorrhea);
    aws_string_secure_destroy((void *)deadbeef);
    return 0;
}
