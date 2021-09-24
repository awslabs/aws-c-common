/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/profile.h>
#include <aws/common/string.h>

static int s_do_aws_profile_fatal_parse_test(
    struct aws_allocator *allocator,
    const struct aws_string *profile_contents) {
    struct aws_byte_cursor contents = aws_byte_cursor_from_string(profile_contents);
    struct aws_byte_buf buffer;
    aws_byte_buf_init_copy_from_cursor(&buffer, allocator, contents);

    struct aws_profile_collection *profile_collection =
        aws_profile_collection_new_from_buffer(allocator, &buffer, AWS_PST_NONE);

    aws_byte_buf_clean_up(&buffer);

    ASSERT_TRUE(profile_collection == NULL);

    return 0;
}

#define AWS_PROFILE_PARSE_FAILURE_TEST(test_name, content_string)                                                      \
    static int s_##test_name(struct aws_allocator *allocator, void *ctx) {                                             \
        (void)ctx;                                                                                                     \
        return s_do_aws_profile_fatal_parse_test(allocator, content_string);                                           \
    }                                                                                                                  \
    AWS_TEST_CASE(test_name, s_##test_name);

AWS_STATIC_STRING_FROM_LITERAL(
    s_early_property_profile_file,
    "bad=value\n"
    "[default]\r\n"
    "good=value\r\n");

AWS_PROFILE_PARSE_FAILURE_TEST(aws_profile_early_property_parse_failure_test, s_early_property_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_missing_bracket_profile_file,
    "[default \r\n"
    "good=value\r\n");

AWS_PROFILE_PARSE_FAILURE_TEST(aws_profile_missing_bracket_parse_failure_test, s_missing_bracket_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_missing_assignment_profile_file,
    "[default]  \r\n"
    "bad\r\n");

AWS_PROFILE_PARSE_FAILURE_TEST(aws_profile_missing_assignment_parse_failure_test, s_missing_assignment_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_missing_property_key_profile_file,
    "[default]  ; hello\r\n"
    "=bad\r\n");

AWS_PROFILE_PARSE_FAILURE_TEST(aws_profile_missing_property_key_parse_failure_test, s_missing_property_key_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_early_continuation_profile_file,
    "[default]\r\n"
    "  continuation\n");

AWS_PROFILE_PARSE_FAILURE_TEST(aws_profile_early_continuation_parse_failure_test, s_early_continuation_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_illegal_continuation1_profile_file,
    "[default]\r\n"
    "s3 =\n"
    "  badcontinuation\n");

AWS_PROFILE_PARSE_FAILURE_TEST(
    aws_profile_illegal_continuation1_parse_failure_test,
    s_illegal_continuation1_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_illegal_continuation2_profile_file,
    "[default]\r\n"
    "s3 =\n"
    "  ^^badcontinuation\n");

AWS_PROFILE_PARSE_FAILURE_TEST(
    aws_profile_illegal_continuation2_parse_failure_test,
    s_illegal_continuation2_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_illegal_continuation3_profile_file,
    "[default]\r\n"
    "s3 =\n"
    "  =value\n");

AWS_PROFILE_PARSE_FAILURE_TEST(
    aws_profile_illegal_continuation3_parse_failure_test,
    s_illegal_continuation3_profile_file)

AWS_STATIC_STRING_FROM_LITERAL(
    s_continuation_reset_on_new_profile_file,
    "[profile foo]\nname = value\n[profile foo]\n -continued");

AWS_PROFILE_PARSE_FAILURE_TEST(
    aws_profile_continuation_reset_on_new_profile_parse_failure_test,
    s_continuation_reset_on_new_profile_file)
