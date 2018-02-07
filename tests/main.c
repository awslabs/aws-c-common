
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
#include <array_list_test.c>
#include <encoding_test.c>

int main(int argc, char *argv[]) {

    AWS_RUN_TEST_CASES(&raise_errors_test,
                       &reset_errors_test,
                       &error_callback_test,
                       &unknown_error_code_in_slot_test,
                       &unknown_error_code_no_slot_test,
                       &unknown_error_code_range_too_large_test,
                       &error_code_cross_thread_test,
                       &thread_creation_join_test,
                       &mutex_aquire_release_test,
                       &mutex_is_actually_mutex_test,
                       &high_res_clock_increments_test,
                       &sys_clock_increments_test,
                       &raise_errors_test,
                       &reset_errors_test,
                       &error_callback_test,
                       &unknown_error_code_in_slot_test,
                       &unknown_error_code_no_slot_test,
                       &unknown_error_code_range_too_large_test,
                       &array_list_order_push_back_pop_front_test,
                       &array_list_order_push_back_pop_back_test,
                       &array_list_exponential_mem_model_test,
                       &array_list_exponential_mem_model_iteration_test,
                       &array_list_iteration_test,
                       &array_list_iteration_by_ptr_test,
                       &array_list_preallocated_iteration_test,
                       &array_list_preallocated_push_test,
                       &array_list_shrink_to_fit_test,
                       &array_list_shrink_to_fit_static_test,
                       &array_list_clear_test,
                       &array_list_copy_test,
                       &array_list_not_enough_space_test,
                       &array_list_not_enough_space_test_failure,
                       &hex_encoding_test_case_empty_test,
                       &hex_encoding_test_case_f_test,
                       &hex_encoding_test_case_fo_test,
                       &hex_encoding_test_case_foo_test,
                       &hex_encoding_test_case_foob_test,
                       &hex_encoding_test_case_fooba_test,
                       &hex_encoding_test_case_foobar_test,
                       &hex_encoding_test_case_missing_leading_zero,
                       &hex_encoding_invalid_buffer_size_test,
                       &hex_encoding_overflow_test,
                       &hex_encoding_invalid_string_test,
                       &base64_encoding_test_case_empty_test,
                       &base64_encoding_test_case_f_test,
                       &base64_encoding_test_case_fo_test,
                       &base64_encoding_test_case_foo_test,
                       &base64_encoding_test_case_foob_test,
                       &base64_encoding_test_case_fooba_test,
                       &base64_encoding_test_case_foobar_test,
                       &base64_encoding_buffer_size_too_small_test,
                       &base64_encoding_buffer_size_overflow_test,
                       &base64_encoding_buffer_size_invalid_test,
                       &base64_encoding_invalid_buffer_test,
                       &base64_encoding_invalid_padding_test,
                       &uint64_buffer_test,
                       &uint64_buffer_non_aligned_test,
                       &uint32_buffer_test,
                       &uint32_buffer_non_aligned_test,
                       &uint24_buffer_test,
                       &uint24_buffer_non_aligned_test,
                       &uint16_buffer_test,
                       &uint16_buffer_non_aligned_test,
                       &uint16_buffer_signed_positive_test,
                       &uint16_buffer_signed_negative_test)
}
