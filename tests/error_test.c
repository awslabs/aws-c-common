/*
 *  Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License").
 *  You may not use this file except in compliance with the License.
 *  A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 *  or in the "license" file accompanying this file. This file is distributed
 *  on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 *  express or implied. See the License for the specific language governing
 *  permissions and limitations under the License.
 */

#include <aws_test_harness.h>

static struct aws_error_info errors[] = {
    AWS_DEFINE_ERROR_INFO(test_error_1, 1000, "test error 1", "test lib"),
    AWS_DEFINE_ERROR_INFO(test_error_2, 1001, "test error 2", "test lib"),
};

static struct aws_error_info_list errors_list = {
        .error_list = errors,
        .count = sizeof(errors) / sizeof(struct aws_error_info),
};

static void setup_errors_test_fn(struct aws_allocator *config, void *ctx) {
    aws_reset_error();
    aws_set_global_error_handler_fn(NULL, NULL);
    aws_set_thread_local_error_handler_fn(NULL, NULL);
    aws_register_error_info(&errors_list);
}

static void teardown_errors_test_fn(struct aws_allocator *config, void *ctx) {
    aws_reset_error();
    aws_set_global_error_handler_fn(NULL, NULL);
    aws_set_thread_local_error_handler_fn(NULL, NULL);
}

static int raise_errors_test_fn(struct aws_allocator *config, void *ctx) {

    int error = aws_last_error();

    ASSERT_NULL(error, "error should be initialized to NULL");
    ASSERT_INT_EQUALS(0, aws_last_error(), "error code should be initialized to 0");

    struct aws_error_info test_error_1 = errors[0];
    struct aws_error_info test_error_2 = errors[1];

    ASSERT_INT_EQUALS(-1, aws_raise_error(test_error_1.error_code), "Raise error should return failure code.");
    error = aws_last_error();
    ASSERT_INT_EQUALS(test_error_1.error_code, error, "Expected error code %d, but was %d",
                      test_error_1.error_code, error);

    ASSERT_STR_EQUALS(test_error_1.error_str, aws_error_str(error), "Expected error string %s, but got %s",
                      test_error_1.error_str, aws_error_str(error));
    ASSERT_STR_EQUALS(test_error_1.lib_name, aws_error_lib_name(error), "Expected error libname %s, but got %s",
                      test_error_1.lib_name, aws_error_lib_name(error));

    ASSERT_INT_EQUALS(-1, aws_raise_error(test_error_2.error_code), "Raise error should return failure code.");
    error = aws_last_error();

    ASSERT_INT_EQUALS(test_error_2.error_code, error, "Expected error code %d, but was %d",
                      test_error_2.error_code, error);

    error = aws_last_error();
    ASSERT_NOT_NULL(error, "last error should not have been null");
    ASSERT_STR_EQUALS(test_error_2.error_str, aws_error_str(error), "Expected error string %s, but got %s",
                      test_error_2.error_str, aws_error_str(error));
    ASSERT_STR_EQUALS(test_error_2.lib_name, aws_error_lib_name(error), "Expected error libname %s, but got %s",
                      test_error_2.lib_name, aws_error_lib_name(error));

    aws_reset_error();
    error = aws_last_error();
    ASSERT_NULL(error, "error should be reset to NULL");
    ASSERT_INT_EQUALS(0, aws_last_error(), "error code should be reset to 0");
    return 0;
}


static int reset_errors_test_fn(struct aws_allocator *config, void *ctx) {

    struct aws_error_info test_error_1 = errors[0];
    struct aws_error_info test_error_2 = errors[1];

    aws_raise_error(test_error_2.error_code);
    aws_restore_error(test_error_1.error_code);

    int error = aws_last_error();
    ASSERT_NOT_NULL(error, "last error should not have been null");
    ASSERT_INT_EQUALS(test_error_1.error_code, error, "Expected error code %d, but was %d",
                      test_error_1.error_code, error);
    ASSERT_STR_EQUALS(test_error_1.error_str, aws_error_str(error), "Expected error string %s, but got %s",
                      test_error_1.error_str, aws_error_str(error));
    ASSERT_STR_EQUALS(test_error_1.lib_name, aws_error_lib_name(error), "Expected error libname %s, but got %s",
                      test_error_1.lib_name, aws_error_lib_name(error));

    return 0;
}

struct error_test_cb_data {
    int global_cb_called;
    int tl_cb_called;
    int last_seen;
};

static void error_test_global_cb(int err, void *ctx) {
    struct error_test_cb_data *cb_data = (struct error_test_cb_data *)ctx;
    cb_data->global_cb_called = 1;
    cb_data->last_seen = err;
}

static void error_test_thread_local_cb(int err, void *ctx) {
    struct error_test_cb_data *cb_data = (struct error_test_cb_data *)ctx;
    cb_data->tl_cb_called = 1;
    cb_data->last_seen = err;
}

static int error_callback_test_fn(struct aws_allocator *config, void *ctx) {

    struct error_test_cb_data cb_data = {
            .last_seen = 0,
            .global_cb_called = 0,
            .tl_cb_called = 0
    };

    struct aws_error_info test_error_1 = errors[0];
    struct aws_error_info test_error_2 = errors[1];

    aws_error_handler old_fn = aws_set_global_error_handler_fn(error_test_global_cb, &cb_data);
    ASSERT_NULL(old_fn, "setting the global error callback the first time should return null");
    aws_raise_error(test_error_1.error_code);

    ASSERT_NOT_NULL(cb_data.last_seen, "last error should not have been null");
    ASSERT_TRUE(cb_data.global_cb_called, "Global Callback should have been invoked");
    ASSERT_FALSE(cb_data.tl_cb_called, "Thread Local Callback should not have been invoked");

    ASSERT_INT_EQUALS(test_error_1.error_code, cb_data.last_seen, "Expected error code %d, but was %d",
                      test_error_1.error_code, cb_data.last_seen);
    ASSERT_STR_EQUALS(test_error_1.error_str, aws_error_str(cb_data.last_seen), "Expected error string %s, but got %s",
                      test_error_1.error_str, aws_error_str(cb_data.last_seen));
    ASSERT_STR_EQUALS(test_error_1.lib_name, aws_error_lib_name(cb_data.last_seen), "Expected error libname %s, but got %s",
                      test_error_1.lib_name, aws_error_lib_name(cb_data.last_seen));

    cb_data.last_seen = 0;
    cb_data.global_cb_called = 0;
    old_fn = aws_set_thread_local_error_handler_fn(error_test_thread_local_cb, &cb_data);
    ASSERT_NULL(old_fn, "setting the global error callback the first time should return null");

    aws_raise_error(test_error_2.error_code);
    ASSERT_INT_EQUALS(test_error_2.error_code, aws_last_error(), "Expected error code %d, but was %d",
                      test_error_2.error_code, aws_last_error());


    ASSERT_NOT_NULL(cb_data.last_seen, "last error should not have been null");
    ASSERT_FALSE(cb_data.global_cb_called, "Global Callback should not have been invoked");
    ASSERT_TRUE(cb_data.tl_cb_called, "Thread local Callback should have been invoked");

    ASSERT_INT_EQUALS(test_error_2.error_code, cb_data.last_seen, "Expected error code %d, but was %d",
                      test_error_2.error_code, cb_data.last_seen);
    ASSERT_STR_EQUALS(test_error_2.error_str, aws_error_str(cb_data.last_seen), "Expected error string %s, but got %s",
                      test_error_2.error_str, aws_error_str(cb_data.last_seen));
    ASSERT_STR_EQUALS(test_error_2.lib_name, aws_error_lib_name(cb_data.last_seen), "Expected error libname %s, but got %s",
                      test_error_2.lib_name, aws_error_lib_name(cb_data.last_seen));

    old_fn = aws_set_thread_local_error_handler_fn(NULL, NULL);
    ASSERT_INT_EQUALS(error_test_thread_local_cb, old_fn, "Setting a new thread local error callback should have returned the most recent value");
    old_fn = aws_set_global_error_handler_fn(NULL, NULL);
    ASSERT_INT_EQUALS(error_test_global_cb, old_fn, "Setting a new global error callback should have returned the most recent value");

    return 0;
}

static int unknown_error_code_in_slot_test_fn(struct aws_allocator *config, void *ctx) {

    int error = aws_last_error();

    ASSERT_NULL(error, "error should be initialized to NULL");
    ASSERT_INT_EQUALS(0, aws_last_error(), "error code should be initialized to 0");

    struct aws_error_info test_error_2 = errors[1];

    aws_raise_error(test_error_2.error_code + 1);
    error = aws_last_error();
    /* error code should still propogate */
    ASSERT_INT_EQUALS(test_error_2.error_code + 1, error, "Expected error code %d, but was %d",
                      test_error_2.error_code + 1, error);

    /* string should be invalid though */
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_str(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_lib_name(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_lib_name(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_debug_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_debug_str(error));

    return 0;
}

static int unknown_error_code_no_slot_test_fn(struct aws_allocator *config, void *ctx) {

    int error = aws_last_error();

    ASSERT_NULL(error, "error should be initialized to NULL");
    ASSERT_INT_EQUALS(0, aws_last_error(), "error code should be initialized to 0");

    int non_slotted_error_code = 3000;
    aws_raise_error(non_slotted_error_code);
    error = aws_last_error();
    /* error code should still propogate */
    ASSERT_INT_EQUALS(non_slotted_error_code, error, "Expected error code %d, but was %d",
                      non_slotted_error_code, error);

    /* string should be invalid though */
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_str(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_lib_name(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_lib_name(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_debug_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_debug_str(error));

    return 0;
}

static int unknown_error_code_range_too_large_test_fn(struct aws_allocator *config, void *ctx) {

    int error = aws_last_error();

    ASSERT_NULL(error, "error should be initialized to NULL");
    ASSERT_INT_EQUALS(0, aws_last_error(), "error code should be initialized to 0");

    int oor_error_code = 10001;
    aws_raise_error(oor_error_code);
    error = aws_last_error();
    /* error code should still propogate */
    ASSERT_INT_EQUALS(oor_error_code, error, "Expected error code %d, but was %d",
                      oor_error_code, error);

    /* string should be invalid though */
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_str(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_lib_name(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_lib_name(error));
    ASSERT_STR_EQUALS("Unknown Error Code", aws_error_debug_str(error), "Expected error string %s, but got %s",
                      "Unknown Error Code", aws_error_debug_str(error));

    return 0;
}

/* TODO: after adding threading abstraction, add a test to make sure thread local apis work as expected */

AWS_TEST_CASE_FIXTURE(raise_errors_test, setup_errors_test_fn, raise_errors_test_fn, teardown_errors_test_fn, NULL)
AWS_TEST_CASE_FIXTURE(error_callback_test, setup_errors_test_fn, error_callback_test_fn, teardown_errors_test_fn, NULL)
AWS_TEST_CASE_FIXTURE(reset_errors_test, setup_errors_test_fn, reset_errors_test_fn, teardown_errors_test_fn, NULL)
AWS_TEST_CASE_FIXTURE(unknown_error_code_in_slot_test, setup_errors_test_fn, unknown_error_code_in_slot_test_fn, teardown_errors_test_fn, NULL)
AWS_TEST_CASE_FIXTURE(unknown_error_code_no_slot_test, setup_errors_test_fn, unknown_error_code_no_slot_test_fn, teardown_errors_test_fn, NULL)
AWS_TEST_CASE_FIXTURE(unknown_error_code_range_too_large_test, setup_errors_test_fn, unknown_error_code_range_too_large_test_fn, teardown_errors_test_fn, NULL)
