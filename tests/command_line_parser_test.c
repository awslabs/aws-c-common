/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/command_line_parser.h>
#include <aws/testing/aws_test_harness.h>

/* If this is tested from a dynamic library, the static state needs to be reset */
static void s_reset_static_state(void) {
    aws_cli_optind = 1;
}

static int s_test_short_argument_parse_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    struct aws_cli_option options[] = {
        {.name = NULL, .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .flag = NULL, .val = 'a'},
        {.name = "beeee", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .flag = NULL, .val = 'b'},
        {.name = NULL, .has_arg = AWS_CLI_OPTIONS_OPTIONAL_ARGUMENT, .flag = NULL, .val = 'c'},
        {.name = NULL, .has_arg = 0, .flag = NULL, .val = 0},
    };

    char *const args[] = {
        "prog-name",
        "-a",
        "-b",
        "bval",
        "-c",
    };
    int argc = 5;
    int longindex = 0;
    s_reset_static_state();
    int arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('a', arg);
    ASSERT_INT_EQUALS(0, longindex);
    ASSERT_INT_EQUALS(2, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('b', arg);
    ASSERT_STR_EQUALS("bval", aws_cli_optarg);
    ASSERT_INT_EQUALS(1, longindex);
    ASSERT_INT_EQUALS(4, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('c', arg);
    ASSERT_INT_EQUALS(2, longindex);
    ASSERT_INT_EQUALS(-1, aws_cli_getopt_long(argc, args, "ab:c", options, &longindex));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(short_argument_parse, s_test_short_argument_parse_fn)

static int s_test_long_argument_parse_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    struct aws_cli_option options[] = {
        {.name = "aaee", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .flag = NULL, .val = 'a'},
        {.name = "beeee", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .flag = NULL, .val = 'b'},
        {.name = "cceeee", .has_arg = AWS_CLI_OPTIONS_OPTIONAL_ARGUMENT, .flag = NULL, .val = 'c'},
        {.name = NULL, .has_arg = 0, .flag = NULL, .val = 0},
    };

    char *const args[] = {
        "prog-name",
        "--aaee",
        "--beeee",
        "bval",
        "-cceeee",
    };
    int argc = 5;
    int longindex = 0;
    s_reset_static_state();
    int arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('a', arg);
    ASSERT_INT_EQUALS(0, longindex);
    ASSERT_INT_EQUALS(2, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('b', arg);
    ASSERT_STR_EQUALS("bval", aws_cli_optarg);
    ASSERT_INT_EQUALS(1, longindex);
    ASSERT_INT_EQUALS(4, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('c', arg);
    ASSERT_INT_EQUALS(2, longindex);

    ASSERT_INT_EQUALS(-1, aws_cli_getopt_long(argc, args, "ab:c", options, &longindex));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(long_argument_parse, s_test_long_argument_parse_fn)

static int s_test_unqualified_argument_parse_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    struct aws_cli_option options[] = {
        {.name = "aaee", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .flag = NULL, .val = 'a'},
        {.name = "beeee", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .flag = NULL, .val = 'b'},
        {.name = "cceeee", .has_arg = AWS_CLI_OPTIONS_OPTIONAL_ARGUMENT, .flag = NULL, .val = 'c'},
        {.name = NULL, .has_arg = 0, .flag = NULL, .val = 0},
    };

    char *const args[] = {"prog-name", "-a", "--beeee", "bval", "-c", "operand"};
    int argc = 6;
    int longindex = 0;
    s_reset_static_state();
    int arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('a', arg);
    ASSERT_INT_EQUALS(0, longindex);
    ASSERT_INT_EQUALS(2, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('b', arg);
    ASSERT_STR_EQUALS("bval", aws_cli_optarg);
    ASSERT_INT_EQUALS(1, longindex);
    ASSERT_INT_EQUALS(4, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('c', arg);
    ASSERT_INT_EQUALS(2, longindex);

    ASSERT_INT_EQUALS(0x02, aws_cli_getopt_long(argc, args, "ab:c", options, &longindex));
    ASSERT_TRUE(aws_cli_optind == argc);
    ASSERT_STR_EQUALS("operand", aws_cli_positional_arg);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(unqualified_argument_parse, s_test_unqualified_argument_parse_fn)

static int s_test_unknown_argument_parse_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;
    struct aws_cli_option options[] = {
        {.name = "aaee", .has_arg = AWS_CLI_OPTIONS_NO_ARGUMENT, .flag = NULL, .val = 'a'},
        {.name = "beeee", .has_arg = AWS_CLI_OPTIONS_REQUIRED_ARGUMENT, .flag = NULL, .val = 'b'},
        {.name = "cceeee", .has_arg = AWS_CLI_OPTIONS_OPTIONAL_ARGUMENT, .flag = NULL, .val = 'c'},
        {.name = NULL, .has_arg = 0, .flag = NULL, .val = 0},
    };

    char *const args[] = {"prog-name", "-BOO!", "--beeee", "bval", "-c", "operand"};
    int argc = 6;
    int longindex = 0;
    s_reset_static_state();
    int arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('?', arg);
    ASSERT_INT_EQUALS(0, longindex);
    ASSERT_INT_EQUALS(2, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('b', arg);
    ASSERT_STR_EQUALS("bval", aws_cli_optarg);
    ASSERT_INT_EQUALS(1, longindex);
    ASSERT_INT_EQUALS(4, aws_cli_optind);
    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_INT_EQUALS('c', arg);
    ASSERT_INT_EQUALS(2, longindex);

    arg = aws_cli_getopt_long(argc, args, "ab:c", options, &longindex);
    ASSERT_TRUE(arg == 0x02);
    ASSERT_TRUE(aws_cli_optind == argc);
    ASSERT_STR_EQUALS("operand", aws_cli_positional_arg);

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(unknown_argument_parse, s_test_unknown_argument_parse_fn)

struct subcommand_dispatch_data {
    const char *command_name;
    int argc;
    char *const *argv;
};

static int s_subcommand_callback(int argc, char *const argv[], const char *command_name, void *user_data) {
    struct subcommand_dispatch_data *dispatch_data = user_data;
    dispatch_data->command_name = command_name;
    dispatch_data->argc = argc;
    dispatch_data->argv = argv;

    return AWS_OP_SUCCESS;
}

static int s_test_command_dispatch_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    struct subcommand_dispatch_data dispatch_data;
    AWS_ZERO_STRUCT(dispatch_data);

    struct aws_cli_subcommand_dispatch dispatch_table[] = {
        {
            .command_name = "command1",
            .subcommand_fn = s_subcommand_callback,
        },
        {
            .command_name = "command2",
            .subcommand_fn = s_subcommand_callback,
        },
    };

    char *const args_1[] = {"prog-name", "command1", "-BOO!", "--beeee", "bval", "-c", "operand"};
    ASSERT_SUCCESS(aws_cli_dispatch_on_subcommand(7, args_1, dispatch_table, 2, &dispatch_data));
    ASSERT_STR_EQUALS("command1", dispatch_data.command_name);
    ASSERT_INT_EQUALS(6, dispatch_data.argc);
    ASSERT_STR_EQUALS("command1", dispatch_data.argv[0]);

    AWS_ZERO_STRUCT(dispatch_data);
    char *const args_2[] = {"prog-name", "command2", "-BOO!", "--beeee", "bval", "-c", "operand"};
    ASSERT_SUCCESS(aws_cli_dispatch_on_subcommand(7, args_2, dispatch_table, 2, &dispatch_data));
    ASSERT_STR_EQUALS("command2", dispatch_data.command_name);
    ASSERT_INT_EQUALS(6, dispatch_data.argc);
    ASSERT_STR_EQUALS("command2", dispatch_data.argv[0]);

    char *const args_3[] = {"prog-name", "command3", "-BOO!", "--beeee", "bval", "-c", "operand"};
    ASSERT_ERROR(AWS_ERROR_UNIMPLEMENTED, aws_cli_dispatch_on_subcommand(7, args_3, dispatch_table, 2, &dispatch_data));

    char *const args_4[] = {"prog-name"};
    ASSERT_ERROR(
        AWS_ERROR_INVALID_ARGUMENT, aws_cli_dispatch_on_subcommand(1, args_4, dispatch_table, 2, &dispatch_data));

    return AWS_OP_SUCCESS;
}

AWS_TEST_CASE(test_command_dispatch, s_test_command_dispatch_fn)
