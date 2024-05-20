/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/cross_process_lock.h>
#include <aws/common/environment.h>
#include <aws/common/process.h>
#include <aws/testing/aws_test_harness.h>

static int s_test_cross_process_lock_works_in_proc(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_byte_cursor lock_nonce = aws_byte_cursor_from_c_str("lock_nonce");
    struct aws_cross_process_lock *instance_lock = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
    ASSERT_NOT_NULL(instance_lock);

    struct aws_cross_process_lock *should_be_null = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
    ASSERT_NULL(should_be_null);

    aws_cross_process_lock_release(instance_lock);
    struct aws_cross_process_lock *should_not_be_null = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
    ASSERT_NOT_NULL(should_not_be_null);
    aws_cross_process_lock_release(should_not_be_null);

    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(test_cross_process_lock_works_in_proc, s_test_cross_process_lock_works_in_proc)

static int s_cross_process_lock_mp_test_runner(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);

    /* so the test runner doesn't actually run the portion of the test we want to test unless we're invoking it as a
     * subprocess. */
    struct aws_string *test_run_gate = aws_string_new_from_c_str(allocator, "aws_crt_test_run_gate");
    struct aws_string *output_val = NULL;
    if (aws_get_environment_value(allocator, test_run_gate, &output_val) == AWS_OP_SUCCESS && output_val) {
        aws_string_destroy(output_val);
        struct aws_byte_cursor lock_nonce = aws_byte_cursor_from_c_str("lock_mp_nonce");
        struct aws_cross_process_lock *instance_lock = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
        ASSERT_NOT_NULL(instance_lock);

        aws_cross_process_lock_release(instance_lock);
    }
    aws_string_destroy(test_run_gate);
    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(cross_process_lock_mp_test_runner, s_cross_process_lock_mp_test_runner)

static int s_test_cross_process_lock_works_cross_proc(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);

    struct aws_string *test_run_gate = aws_string_new_from_c_str(allocator, "aws_crt_test_run_gate");
    struct aws_string *test_run_gate_val = aws_string_new_from_c_str(allocator, "ON");

    /* so the test runner doesn't actually run the portion of the test we want to test unless we're invoking it from
     * here. */
    ASSERT_SUCCESS(aws_set_environment_value(test_run_gate, test_run_gate_val));
    aws_string_destroy(test_run_gate_val);
    aws_string_destroy(test_run_gate);

    /* Invoke the test runner in a new process for ease so cmake automatically does the work for us. */
    struct aws_run_command_options command_options = {
#ifdef _WIN32
        .command = "aws-c-common-tests cross_process_lock_mp_test_runner",
#else
        .command = "./aws-c-common-tests cross_process_lock_mp_test_runner",
#endif /* _WIN32 */
    };

    struct aws_run_command_result result;
    AWS_ZERO_STRUCT(result);

    ASSERT_SUCCESS(aws_run_command(allocator, &command_options, &result));
    ASSERT_TRUE(result.ret_code == 0);
    aws_run_command_result_cleanup(&result);
    AWS_ZERO_STRUCT(result);
    struct aws_byte_cursor lock_nonce = aws_byte_cursor_from_c_str("lock_mp_nonce");
    struct aws_cross_process_lock *instance_lock = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
    ASSERT_NOT_NULL(instance_lock);

    ASSERT_SUCCESS(aws_run_command(allocator, &command_options, &result));
    ASSERT_FALSE(result.ret_code == 0);
    aws_run_command_result_cleanup(&result);

    aws_cross_process_lock_release(instance_lock);
    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(test_cross_process_lock_works_cross_proc, s_test_cross_process_lock_works_cross_proc)

static int s_test_cross_process_lock_invalid_nonce(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    aws_common_library_init(allocator);
#ifdef _WIN32
    struct aws_byte_cursor lock_nonce = aws_byte_cursor_from_c_str("invalid\\lock_nonce");
#else
    struct aws_byte_cursor lock_nonce = aws_byte_cursor_from_c_str("invalid/lock_nonce");
#endif /* _WIN32 */

    struct aws_cross_process_lock *instance_lock = aws_cross_process_lock_try_acquire(allocator, lock_nonce);
    ASSERT_NULL(instance_lock);
    ASSERT_INT_EQUALS(AWS_ERROR_INVALID_ARGUMENT, aws_last_error());

    aws_common_library_clean_up();

    return AWS_OP_SUCCESS;
}
AWS_TEST_CASE(test_cross_process_lock_invalid_nonce_fails, s_test_cross_process_lock_invalid_nonce)
