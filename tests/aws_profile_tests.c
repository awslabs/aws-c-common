/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/testing/aws_test_harness.h>

#include <aws/common/environment.h>
#include <aws/common/aws_profile.h>
#include <aws/common/string.h>

#define EXPECT_PROFILE_COUNT(profile_collection, profile_count)                                                        \
    { ASSERT_TRUE(aws_profile_collection_get_profile_count(profile_collection) == (profile_count)); }

#define EXPECT_PROFILE(profile_collection, profile_name)                                                               \
    {                                                                                                                  \
        struct aws_string *profile_name_str = aws_string_new_from_c_str(allocator, profile_name);                      \
        struct aws_profile *profile = aws_profile_collection_get_profile(profile_collection, profile_name_str);        \
        aws_string_destroy(profile_name_str);                                                                          \
        ASSERT_TRUE(profile != NULL);                                                                                  \
    }

#define EXPECT_PROPERTY_COUNT(profile_collection, profile_name, expected_property_count)                               \
    {                                                                                                                  \
        struct aws_string *profile_name_str = aws_string_new_from_c_str(allocator, profile_name);                      \
        struct aws_profile *profile = aws_profile_collection_get_profile(profile_collection, profile_name_str);        \
        aws_string_destroy(profile_name_str);                                                                          \
        ASSERT_TRUE(aws_profile_get_property_count(profile) == (expected_property_count));                             \
    }

#define EXPECT_PROPERTY(profile_collection, profile_name, property_name, expected_property_value)                      \
    {                                                                                                                  \
        struct aws_string *profile_name_str = aws_string_new_from_c_str(allocator, profile_name);                      \
        struct aws_profile *profile = aws_profile_collection_get_profile(profile_collection, profile_name_str);        \
        struct aws_string *property_name_str = aws_string_new_from_c_str(allocator, property_name);                    \
        struct aws_profile_property *property = aws_profile_get_property(profile, property_name_str);                  \
        aws_string_destroy(property_name_str);                                                                         \
        aws_string_destroy(profile_name_str);                                                                          \
        ASSERT_TRUE(property != NULL && strcmp(expected_property_value, aws_string_c_str(property->value)) == 0);      \
    }

#define EXPECT_SUB_PROPERTY_COUNT(profile_collection, profile_name, property_name, expected_sub_property_count)        \
    {                                                                                                                  \
        struct aws_string *profile_name_str = aws_string_new_from_c_str(allocator, profile_name);                      \
        struct aws_profile *profile = aws_profile_collection_get_profile(profile_collection, profile_name_str);        \
        struct aws_string *property_name_str = aws_string_new_from_c_str(allocator, property_name);                    \
        struct aws_profile_property *property = aws_profile_get_property(profile, property_name_str);                  \
        aws_string_destroy(property_name_str);                                                                         \
        aws_string_destroy(profile_name_str);                                                                          \
        ASSERT_UINT_EQUALS((expected_sub_property_count), aws_profile_property_get_sub_property_count(property));      \
    }

#define EXPECT_SUB_PROPERTY(                                                                                           \
    profile_collection, profile_name, property_name, sub_property_name, expected_sub_property_value)                   \
    {                                                                                                                  \
        struct aws_string *profile_name_str = aws_string_new_from_c_str(allocator, profile_name);                      \
        struct aws_profile *profile = aws_profile_collection_get_profile(profile_collection, profile_name_str);        \
        struct aws_string *property_name_str = aws_string_new_from_c_str(allocator, property_name);                    \
        struct aws_profile_property *property = aws_profile_get_property(profile, property_name_str);                  \
        struct aws_string *sub_property_name_str = aws_string_new_from_c_str(allocator, sub_property_name);            \
        const struct aws_string *sub_property_value =                                                                  \
            aws_profile_property_get_sub_property(property, sub_property_name_str);                                    \
        aws_string_destroy(sub_property_name_str);                                                                     \
        aws_string_destroy(property_name_str);                                                                         \
        aws_string_destroy(profile_name_str);                                                                          \
        ASSERT_TRUE(strcmp(expected_sub_property_value, aws_string_c_str(sub_property_value)) == 0);                   \
    }

/*
 * profile collection setup
 */
struct aws_profile_collection *aws_prepare_profile_test(
    struct aws_allocator *allocator,
    const struct aws_string *profile_contents,
    enum aws_profile_source_type source) {

    struct aws_byte_cursor contents = aws_byte_cursor_from_string(profile_contents);
    struct aws_byte_buf buffer;
    AWS_ZERO_STRUCT(buffer);
    aws_byte_buf_init_copy_from_cursor(&buffer, allocator, contents);

    struct aws_profile_collection *profile_collection =
        aws_profile_collection_new_from_buffer(allocator, &buffer, source);

    aws_byte_buf_clean_up(&buffer);

    return profile_collection;
}

struct aws_profile_collection *aws_prepare_merged_profile_test(
    struct aws_allocator *allocator,
    const struct aws_string *config_contents,
    const struct aws_string *credentials_contents) {

    struct aws_byte_cursor config_cursor = aws_byte_cursor_from_string(config_contents);
    struct aws_byte_buf config_buffer;
    aws_byte_buf_init_copy_from_cursor(&config_buffer, allocator, config_cursor);

    struct aws_profile_collection *config_profile_collection =
        aws_profile_collection_new_from_buffer(allocator, &config_buffer, AWS_PST_CONFIG);

    aws_byte_buf_clean_up(&config_buffer);

    struct aws_byte_cursor credentials_cursor = aws_byte_cursor_from_string(credentials_contents);
    struct aws_byte_buf credentials_buffer;
    aws_byte_buf_init_copy_from_cursor(&credentials_buffer, allocator, credentials_cursor);

    struct aws_profile_collection *credentials_profile_collection =
        aws_profile_collection_new_from_buffer(allocator, &credentials_buffer, AWS_PST_CREDENTIALS);

    aws_byte_buf_clean_up(&credentials_buffer);

    struct aws_profile_collection *merged =
        aws_profile_collection_new_from_merge(allocator, config_profile_collection, credentials_profile_collection);

    if (config_profile_collection) {
        aws_profile_collection_destroy(config_profile_collection);
    }

    if (credentials_profile_collection) {
        aws_profile_collection_destroy(credentials_profile_collection);
    }

    return merged;
}

/*
 * Nothing at all
 */
AWS_STATIC_STRING_FROM_LITERAL(s_empty_string, "");

static int s_aws_profile_empty_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_empty_string, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_empty_test, s_aws_profile_empty_test);

/*
 * A single empty profile
 */
AWS_STATIC_STRING_FROM_LITERAL(s_empty_profile, "[profile foo]");

static int s_aws_profile_empty_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_empty_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_empty_profile_test, s_aws_profile_empty_profile_test);

/*
 * Whitespace in a single empty profile
 */
AWS_STATIC_STRING_FROM_LITERAL(s_whitespace_empty_profile, "[profile \tfoo \t]");

static int s_aws_profile_whitespace_empty_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_whitespace_empty_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_whitespace_empty_profile_test, s_aws_profile_whitespace_empty_profile_test);

/*
 * Tab-separated, a single empty profile
 */
AWS_STATIC_STRING_FROM_LITERAL(s_tab_empty_profile, "[profile\tfoo]");

static int s_aws_profile_tab_empty_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_tab_empty_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_tab_empty_profile_test, s_aws_profile_tab_empty_profile_test);

/*
 * One profile with a single, simple property
 */
AWS_STATIC_STRING_FROM_LITERAL(s_single_simple_property_profile, "[profile foo]\nname = value");

static int s_aws_profile_single_simple_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_single_simple_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_single_simple_property_profile_test, s_aws_profile_single_simple_property_profile_test);

/*
 * Check that = can appear in a property value
 */
AWS_STATIC_STRING_FROM_LITERAL(s_equal_containing_property_profile, "[profile foo]\nname = val=ue");

static int s_aws_profile_equal_containing_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_equal_containing_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "val=ue");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_equal_containing_property_profile_test, s_aws_profile_equal_containing_property_profile_test);

/*
 * Check that non-ascii unicode can appear in a property value
 */
AWS_STATIC_STRING_FROM_LITERAL(s_unicode_containing_property_profile, "[profile foo]\nname = \xF0\x9F\x98\x82");

static int s_aws_profile_unicode_containing_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_unicode_containing_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "\xF0\x9F\x98\x82");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_unicode_containing_property_profile_test,
    s_aws_profile_unicode_containing_property_profile_test);

/*
 * Profiles can contain multiple properties
 */
AWS_STATIC_STRING_FROM_LITERAL(s_multiple_property_profile, "[profile foo]\nname = value\nname2 = value2");

static int s_aws_profile_multiple_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_multiple_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 2);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");
    EXPECT_PROPERTY(profile_collection, "foo", "name2", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_multiple_property_profile_test, s_aws_profile_multiple_property_profile_test);

/*
 * Property name and values get trimmed
 */
AWS_STATIC_STRING_FROM_LITERAL(s_trimmable_property_profile, "[profile foo]\nname \t=  \tvalue \t");

static int s_aws_profile_trimmable_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_trimmable_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_trimmable_property_profile_test, s_aws_profile_trimmable_property_profile_test);

/*
 * Property values can be empty
 */
AWS_STATIC_STRING_FROM_LITERAL(s_empty_property_profile, "[profile foo]\nname =");

static int s_aws_profile_empty_property_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_empty_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_empty_property_profile_test, s_aws_profile_empty_property_profile_test);

/*
 * Multiple empty profiles
 */
AWS_STATIC_STRING_FROM_LITERAL(s_multiple_empty_profile, "[profile foo]\n[profile bar]");

static int s_aws_profile_multiple_empty_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_multiple_empty_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 2);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);
    EXPECT_PROFILE(profile_collection, "bar");
    EXPECT_PROPERTY_COUNT(profile_collection, "bar", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_multiple_empty_profile_test, s_aws_profile_multiple_empty_profile_test);

/*
 * Multiple profiles with properties
 */
AWS_STATIC_STRING_FROM_LITERAL(s_multiple_profile, "[profile foo]\nname = value\n[profile bar]\nname2 = value2");

static int s_aws_profile_multiple_profile_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_multiple_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 2);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");
    EXPECT_PROFILE(profile_collection, "bar");
    EXPECT_PROPERTY_COUNT(profile_collection, "bar", 1);
    EXPECT_PROPERTY(profile_collection, "bar", "name2", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_multiple_profile_test, s_aws_profile_multiple_profile_test);

/*
 * Blank lines are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_blank_lines_ignored_profile,
    "\t \n[profile foo]\n\t\n \nname = value\n\t \n[profile bar]\n \t");

static int s_aws_profile_blank_lines_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_blank_lines_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 2);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");
    EXPECT_PROFILE(profile_collection, "bar");
    EXPECT_PROPERTY_COUNT(profile_collection, "bar", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_blank_lines_ignored_test, s_aws_profile_blank_lines_ignored_test);

/*
 * # comments are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_pound_comments_ignored_profile,
    "# Comment\n[profile foo] # Comment\nname = value # Comment with # sign");

static int s_aws_profile_pound_comments_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_pound_comments_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_pound_comments_ignored_test, s_aws_profile_pound_comments_ignored_test);

/*
 * ; comments are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_semicolon_comments_ignored_profile,
    "; Comment\n[profile foo] ; Comment\nname = value ; Comment with ; sign");

static int s_aws_profile_semicolon_comments_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_semicolon_comments_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_semicolon_comments_ignored_test, s_aws_profile_semicolon_comments_ignored_test);

/*
 * mixed comments are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_mixed_comments_ignored_profile,
    "# Comment\n[profile foo] ; Comment\nname = value # Comment with ; sign");

static int s_aws_profile_mixed_comments_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_mixed_comments_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_mixed_comments_ignored_test, s_aws_profile_mixed_comments_ignored_test);

/*
 * empty comments are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(s_empty_comments_ignored_profile, ";\n[profile foo];\nname = value ;\n");

static int s_aws_profile_empty_comments_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_empty_comments_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_empty_comments_ignored_test, s_aws_profile_empty_comments_ignored_test);

/*
 * comments can be adjacent to profile declaration
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_profile_adjacent_comment_profile,
    "[profile foo]; Adjacent semicolons\n[profile bar]# Adjacent pound signs");

static int s_aws_profile_profile_adjacent_comment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_profile_adjacent_comment_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 2);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);
    EXPECT_PROFILE(profile_collection, "bar");
    EXPECT_PROPERTY_COUNT(profile_collection, "bar", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_profile_adjacent_comment_test, s_aws_profile_profile_adjacent_comment_test);

/*
 * comments adjacent to values are included in the value
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_value_adjacent_comment_profile,
    "[profile foo]\nname = value; Adjacent semicolons\nname2 = value# Adjacent pound signs");

static int s_aws_profile_value_adjacent_comment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_value_adjacent_comment_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 2);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value; Adjacent semicolons");
    EXPECT_PROPERTY(profile_collection, "foo", "name2", "value# Adjacent pound signs");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_value_adjacent_comment_test, s_aws_profile_value_adjacent_comment_test);

/*
 * property values can be continued
 */
AWS_STATIC_STRING_FROM_LITERAL(s_continued_property_value_profile, "[profile foo]\nname = value\n -continued");

static int s_aws_profile_continued_property_value_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_continued_property_value_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value\n-continued");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_continued_property_value_test, s_aws_profile_continued_property_value_test);

/*
 * property values can be continued across multiple lines
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_multiline_continued_property_value_profile,
    "[profile foo]\nname = value\n -continued\n -and-continued");

static int s_aws_profile_multiline_continued_property_value_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_multiline_continued_property_value_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value\n-continued\n-and-continued");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_multiline_continued_property_value_test,
    s_aws_profile_multiline_continued_property_value_test);

/*
 * property value continuations get trimmed
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_continued_property_value_trim_profile,
    "[profile foo]\nname = value\n \t -continued \t ");

static int s_aws_profile_continued_property_value_trim_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_continued_property_value_trim_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value\n-continued");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_continued_property_value_trim_test, s_aws_profile_continued_property_value_trim_test);

/*
 * property value continuations include # comments
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_continued_property_value_pound_comment_profile,
    "[profile foo]\nname = value\n -continued # Comment");

static int s_aws_profile_continued_property_value_pound_comment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_continued_property_value_pound_comment_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value\n-continued # Comment");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_continued_property_value_pound_comment_test,
    s_aws_profile_continued_property_value_pound_comment_test);

/*
 * property value continuations include ; comments
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_continued_property_value_semicolon_comment_profile,
    "[profile foo]\nname = value\n -continued ; Comment");

static int s_aws_profile_continued_property_value_semicolon_comment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_continued_property_value_semicolon_comment_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value\n-continued ; Comment");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_continued_property_value_semicolon_comment_test,
    s_aws_profile_continued_property_value_semicolon_comment_test);

/*
 * duplicate profiles merge properties
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_duplicate_profiles_merge_profile,
    "[profile foo]\nname = value\n[profile foo]\nname2 = value2");

static int s_aws_profile_duplicate_profiles_merge_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_duplicate_profiles_merge_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 2);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");
    EXPECT_PROPERTY(profile_collection, "foo", "name2", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_duplicate_profiles_merge_test, s_aws_profile_duplicate_profiles_merge_test);

/*
 * duplicate properties in a single profile use the last property definition
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_duplicate_properties_last_property_value_profile,
    "[profile foo]\nname = value\nname = value2");

static int s_aws_profile_duplicate_properties_last_property_value_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_duplicate_properties_last_property_value_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_duplicate_properties_last_property_value_test,
    s_aws_profile_duplicate_properties_last_property_value_test);

/*
 * duplicate profiles use the last property definition
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_duplicate_profiles_last_property_value_profile,
    "[profile foo]\nname = value\n[profile foo]\nname = value2");

static int s_aws_profile_duplicate_profiles_last_property_value_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_duplicate_profiles_last_property_value_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_duplicate_profiles_last_property_value_test,
    s_aws_profile_duplicate_profiles_last_property_value_test);

/*
 * Default profile with profile prefix overrides default profile without prefix when profile prefix is first
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_duplicate_default_profiles_property_resolution1_profile,
    "[profile default]\nname = value\n[default]\nname2 = value2");

static int s_aws_profile_duplicate_default_profiles_property_resolution1_test(
    struct aws_allocator *allocator,
    void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_duplicate_default_profiles_property_resolution1_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "default");
    EXPECT_PROPERTY_COUNT(profile_collection, "default", 1);
    EXPECT_PROPERTY(profile_collection, "default", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_duplicate_default_profiles_property_resolution1_test,
    s_aws_profile_duplicate_default_profiles_property_resolution1_test);

/*
 * Default profile with profile prefix overrides default profile without prefix when profile prefix is last
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_duplicate_default_profiles_property_resolution2_profile,
    "[default]\nname2 = value2\n[profile default]\nname = value");

static int s_aws_profile_duplicate_default_profiles_property_resolution2_test(
    struct aws_allocator *allocator,
    void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_duplicate_default_profiles_property_resolution2_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "default");
    EXPECT_PROPERTY_COUNT(profile_collection, "default", 1);
    EXPECT_PROPERTY(profile_collection, "default", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(
    aws_profile_duplicate_default_profiles_property_resolution2_test,
    s_aws_profile_duplicate_default_profiles_property_resolution2_test);

/*
 * Invalid profile names are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(s_invalid_profile_names_config_profile, "[profile in valid]\nname = value");
AWS_STATIC_STRING_FROM_LITERAL(s_invalid_profile_names_credentials_profile, "[in valid 2]\nname2 = value2");

static int s_aws_profile_invalid_profile_names_merge_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection = aws_prepare_merged_profile_test(
        allocator, s_invalid_profile_names_config_profile, s_invalid_profile_names_credentials_profile);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_invalid_profile_names_merge_test, s_aws_profile_invalid_profile_names_merge_test);

/*
 * Invalid property names are ignored
 */
AWS_STATIC_STRING_FROM_LITERAL(s_invalid_property_names_ignored_profile, "[profile foo]\nin valid = value");

static int s_aws_profile_invalid_property_names_ignored_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_invalid_property_names_ignored_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_invalid_property_names_ignored_test, s_aws_profile_invalid_property_names_ignored_test);

/*
 * All valid profile name characters are supported
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_all_valid_profile_characters_profile,
    "[profile ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_]");

static int s_aws_profile_all_valid_profile_characters_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_all_valid_profile_characters_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_");
    EXPECT_PROPERTY_COUNT(profile_collection, "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_all_valid_profile_characters_test, s_aws_profile_all_valid_profile_characters_test);

/*
 * All valid profile name characters are supported
 */
AWS_STATIC_STRING_FROM_LITERAL(
    s_all_valid_property_characters_profile,
    "[profile foo]\nABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_ = value");

static int s_aws_profile_all_valid_property_characters_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_all_valid_property_characters_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(
        profile_collection, "foo", "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_all_valid_property_characters_test, s_aws_profile_all_valid_property_characters_test);

/*
 * Properties can have sub properties
 */
AWS_STATIC_STRING_FROM_LITERAL(s_basic_sub_property_profile, "[profile foo]\ns3 =\n name = value");

static int s_aws_profile_basic_sub_property_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_basic_sub_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "s3", "\nname = value");
    EXPECT_SUB_PROPERTY_COUNT(profile_collection, "foo", "s3", 1);
    EXPECT_SUB_PROPERTY(profile_collection, "foo", "s3", "name", "value");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_basic_sub_property_test, s_aws_profile_basic_sub_property_test);

/*
 * Sub properties can have an empty value
 */

AWS_STATIC_STRING_FROM_LITERAL(s_empty_sub_property_profile, "[profile foo]\ns3 =\n name =");

static int s_aws_profile_empty_sub_property_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_empty_sub_property_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "s3", "\nname =");
    EXPECT_SUB_PROPERTY_COUNT(profile_collection, "foo", "s3", 1);
    EXPECT_SUB_PROPERTY(profile_collection, "foo", "s3", "name", "");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_empty_sub_property_test, s_aws_profile_empty_sub_property_test);

/*
 * An invalid subproperty name is not a fatal parse error
 */

AWS_STATIC_STRING_FROM_LITERAL(s_invalid_sub_property_name_profile, "[profile foo]\ns3 =\n in valid = value");

static int s_aws_profile_invalid_sub_property_name_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_invalid_sub_property_name_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "s3", "\nin valid = value");
    EXPECT_SUB_PROPERTY_COUNT(profile_collection, "foo", "s3", 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_invalid_sub_property_name_test, s_aws_profile_invalid_sub_property_name_test);

/*
 * Sub properties can have blank lines that get ignored
 */

AWS_STATIC_STRING_FROM_LITERAL(
    s_sub_property_blank_line_profile,
    "[profile foo]\ns3 =\n name = value\n\t \n name2 = value2");

static int s_aws_profile_sub_property_blank_line_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_sub_property_blank_line_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "s3", "\nname = value\nname2 = value2");
    EXPECT_SUB_PROPERTY_COUNT(profile_collection, "foo", "s3", 2);
    EXPECT_SUB_PROPERTY(profile_collection, "foo", "s3", "name", "value");
    EXPECT_SUB_PROPERTY(profile_collection, "foo", "s3", "name2", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_sub_property_blank_line_test, s_aws_profile_sub_property_blank_line_test);

/*
 * Profiles duplicated in multiple files are merged.
 */
AWS_STATIC_STRING_FROM_LITERAL(s_basic_duplicate_config_profile, "[profile foo]\nname = value");
AWS_STATIC_STRING_FROM_LITERAL(s_basic_duplicate_credentials_profile, "[foo]\nname2 = value2");

static int s_aws_profile_basic_duplicate_merge_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection = aws_prepare_merged_profile_test(
        allocator, s_basic_duplicate_config_profile, s_basic_duplicate_credentials_profile);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 2);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value");
    EXPECT_PROPERTY(profile_collection, "foo", "name2", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_basic_duplicate_merge_test, s_aws_profile_basic_duplicate_merge_test);

/*
 * When merging default profile in config file, the one without the prefix gets ignored
 */

AWS_STATIC_STRING_FROM_LITERAL(
    s_mixed_prefix_default_profile,
    "[profile default]\nname = value\n[default]\nname2 = value2\n[profile default]\nname3 = value3");

static int s_aws_profile_mixed_prefix_default_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_mixed_prefix_default_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "default");
    EXPECT_PROPERTY_COUNT(profile_collection, "default", 2);
    EXPECT_PROPERTY(profile_collection, "default", "name", "value");
    EXPECT_PROPERTY(profile_collection, "default", "name3", "value3");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_mixed_prefix_default_test, s_aws_profile_mixed_prefix_default_test);

/*
 * Duplicate properties between files use credentials property
 */

AWS_STATIC_STRING_FROM_LITERAL(s_override_duplicate_config_profile, "[profile foo]\nname = value");
AWS_STATIC_STRING_FROM_LITERAL(s_override_duplicate_credentials_profile, "[foo]\nname = value2");

static int s_aws_profile_override_duplicate_merge_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection = aws_prepare_merged_profile_test(
        allocator, s_override_duplicate_config_profile, s_override_duplicate_credentials_profile);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 1);
    EXPECT_PROFILE(profile_collection, "foo");
    EXPECT_PROPERTY_COUNT(profile_collection, "foo", 1);
    EXPECT_PROPERTY(profile_collection, "foo", "name", "value2");

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_override_duplicate_merge_test, s_aws_profile_override_duplicate_merge_test);

/*
 * Non-default config profiles without prefix are ignored
 */

AWS_STATIC_STRING_FROM_LITERAL(s_no_prefix_nondefault_profile, "[foo]\nname = value");

static int s_aws_profile_no_prefix_nondefault_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_no_prefix_nondefault_profile, AWS_PST_CONFIG);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_no_prefix_nondefault_test, s_aws_profile_no_prefix_nondefault_test);

/*
 * Credentials profiles with prefix are ignored
 */

AWS_STATIC_STRING_FROM_LITERAL(s_prefix_credentials_profile, "[profile foo]\nname = value");

static int s_aws_profile_prefix_credentials_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_profile_collection *profile_collection =
        aws_prepare_profile_test(allocator, s_prefix_credentials_profile, AWS_PST_CREDENTIALS);

    ASSERT_TRUE(profile_collection != NULL);
    EXPECT_PROFILE_COUNT(profile_collection, 0);

    aws_profile_collection_destroy(profile_collection);

    return 0;
}

AWS_TEST_CASE(aws_profile_prefix_credentials_test, s_aws_profile_prefix_credentials_test);

AWS_STATIC_STRING_FROM_LITERAL(s_config_override_path, "/tmp/.aws/config");

#ifdef _WIN32
AWS_STATIC_STRING_FROM_LITERAL(s_config_override_path_result, "\\tmp\\.aws\\config");
#else
AWS_STATIC_STRING_FROM_LITERAL(s_config_override_path_result, "/tmp/.aws/config");
#endif /* _WIN32 */

static int s_config_file_path_override_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_cursor override_cursor = aws_byte_cursor_from_string(s_config_override_path);
    struct aws_string *path = aws_get_config_file_path(allocator, &override_cursor);
    ASSERT_TRUE(aws_string_compare(path, s_config_override_path_result) == 0);

    aws_string_destroy(path);

    return 0;
}

AWS_TEST_CASE(config_file_path_override_test, s_config_file_path_override_test);

AWS_STATIC_STRING_FROM_LITERAL(s_config_env_var, "AWS_CONFIG_FILE");

static int s_config_file_path_environment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_set_environment_value(s_config_env_var, s_config_override_path);

    struct aws_string *path = aws_get_config_file_path(allocator, NULL);
    ASSERT_TRUE(aws_string_compare(path, s_config_override_path_result) == 0);

    aws_string_destroy(path);

    return 0;
}

AWS_TEST_CASE(config_file_path_environment_test, s_config_file_path_environment_test);

AWS_STATIC_STRING_FROM_LITERAL(s_credentials_override_path, "/tmp/.aws/credentials");

#ifdef _WIN32
AWS_STATIC_STRING_FROM_LITERAL(s_credentials_override_path_result, "\\tmp\\.aws\\credentials");
#else
AWS_STATIC_STRING_FROM_LITERAL(s_credentials_override_path_result, "/tmp/.aws/credentials");
#endif /* _WIN32 */

static int s_credentials_file_path_override_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    struct aws_byte_cursor override_cursor = aws_byte_cursor_from_string(s_credentials_override_path);
    struct aws_string *path = aws_get_credentials_file_path(allocator, &override_cursor);
    ASSERT_TRUE(aws_string_compare(path, s_credentials_override_path_result) == 0);

    aws_string_destroy(path);

    return 0;
}

AWS_TEST_CASE(credentials_file_path_override_test, s_credentials_file_path_override_test);

AWS_STATIC_STRING_FROM_LITERAL(s_credentials_env_var, "AWS_SHARED_CREDENTIALS_FILE");

static int s_credentials_file_path_environment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_set_environment_value(s_credentials_env_var, s_credentials_override_path);

    struct aws_string *path = aws_get_credentials_file_path(allocator, NULL);
    ASSERT_TRUE(aws_string_compare(path, s_credentials_override_path_result) == 0);

    aws_string_destroy(path);

    return 0;
}

AWS_TEST_CASE(credentials_file_path_environment_test, s_credentials_file_path_environment_test);

AWS_STATIC_STRING_FROM_LITERAL(s_profile_env_var, "AWS_PROFILE");
AWS_STATIC_STRING_FROM_LITERAL(s_profile_override, "NotTheDefault");

static int s_profile_override_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    /* Make sure the environment doesn't affect this test */
    aws_unset_environment_value(s_profile_env_var);

    struct aws_byte_cursor override_cursor = aws_byte_cursor_from_string(s_profile_override);
    struct aws_string *profile_name = aws_get_profile_name(allocator, &override_cursor);
    ASSERT_TRUE(aws_string_compare(profile_name, s_profile_override) == 0);

    aws_string_destroy(profile_name);

    return 0;
}

AWS_TEST_CASE(profile_override_test, s_profile_override_test);

static int s_profile_environment_test(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    aws_set_environment_value(s_profile_env_var, s_profile_override);

    struct aws_string *profile_name = aws_get_profile_name(allocator, NULL);
    ASSERT_TRUE(aws_string_compare(profile_name, s_profile_override) == 0);

    aws_string_destroy(profile_name);

    return 0;
}

AWS_TEST_CASE(profile_environment_test, s_profile_environment_test);
