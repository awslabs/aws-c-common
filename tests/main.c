
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

#include <error_test.c>
#include <thread_test.c>
#include <mutex_test.c>
#include <clock_test.c>

int main(int argc, char *argv[]) {

    AWS_RUN_TEST_CASES(&raise_errors_test, &reset_errors_test, &error_callback_test, &unknown_error_code_in_slot_test,
                       &unknown_error_code_no_slot_test, &unknown_error_code_range_too_large_test, &thread_creation_test,
                       &mutex_aquire_release_test, &mutex_is_actually_mutex_test, &high_res_clock_increments_test,
                       &sys_clock_increments_test)
}
