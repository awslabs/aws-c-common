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

#if _MSC_VER
#pragma warning(disable:4100)
#pragma warning(disable:4221)
#pragma warning(disable:4204)
#endif

#include <encoding_test.c>
#include <cursor_test.c>
#include <error_test.c>
#include <thread_test.c>
#include <mutex_test.c>
#include <condition_variable_test.c>
#include <clock_test.c>
#include <array_list_test.c>
#include <linked_list_test.c>
#include <priority_queue_test.c>
#include <task_scheduler_test.c>
#include <hash_table_test.c>
#include <math_test.c>
#include <split_test.c>
#include <string_test.c>
#include <misc_test.c>
#include <byte_order_test.c>
#include <byte_buf_test.c>
#include <system_info_tests.c>
#include <realloc_test.c>
<<<<<<< HEAD
<<<<<<< HEAD
#include <lru_cache_test.c>
=======
#include <memory_pool_test.c>
>>>>>>> initial skeleton files for memory pool, log, and atomics
=======
#include <memory_pool_test.c>
#include <log_test.h>
#include <lru_cache_test.c>

/* Enables terminal escape sequences for text coloring. */
/* https://docs.microsoft.com/en-us/windows/console/console-virtual-terminal-sequences */
#ifdef _MSC_VER
int EnableVTMode() {
    HANDLE hOut = GetStdHandle(STD_OUTPUT_HANDLE);
    if (hOut == INVALID_HANDLE_VALUE) {
        return AWS_OP_ERR;
    }

    DWORD dwMode = 0;
    if (!GetConsoleMode(hOut, &dwMode)) {
        return AWS_OP_ERR;
    }

    dwMode |= ENABLE_VIRTUAL_TERMINAL_PROCESSING;
    if (!SetConsoleMode(hOut, dwMode)) {
        return AWS_OP_ERR;
    }
    return AWS_OP_SUCCESS;
}
#else
int EnableVTMode() {
    return AWS_OP_ERR;
}
#endif
>>>>>>> fix console colors on windows

int main(int argc, char *argv[]) {

    EnableVTMode();

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
                       &conditional_notify_one,
                       &conditional_notify_all,
                       &conditional_wait_timeout,
                       &high_res_clock_increments_test,
                       &sys_clock_increments_test,
                       &array_list_order_push_back_pop_front_test,
                       &array_list_order_push_back_pop_back_test,
                       &array_list_pop_front_n_test,
                       &array_list_exponential_mem_model_test,
                       &array_list_exponential_mem_model_iteration_test,
                       &array_list_set_at_overwrite_safety,
                       &array_list_iteration_test,
                       &array_list_iteration_by_ptr_test,
                       &array_list_preallocated_iteration_test,
                       &array_list_preallocated_push_test,
                       &array_list_shrink_to_fit_test,
                       &array_list_shrink_to_fit_static_test,
                       &array_list_clear_test,
                       &array_list_copy_test,
                       &array_list_swap_contents_test,
                       &array_list_not_enough_space_test,
                       &array_list_not_enough_space_test_failure,
                       &array_list_of_strings_sort,
                       &array_list_empty_sort,
                       &linked_list_push_back_pop_front,
                       &linked_list_push_front_pop_back,
                       &linked_list_iteration,
                       &priority_queue_push_pop_order_test,
                       &priority_queue_size_and_capacity_test,
                       &priority_queue_random_values_test,
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
                       &base64_encoding_test_zeros,
                       &base64_encoding_test_all_values,
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
                       &uint16_buffer_signed_negative_test,
                       &scheduler_cleanup_cancellation,
                       &scheduler_pops_task_late_test,
                       &scheduler_task_timestamp_test,
                       &scheduler_ordering_test,
                       &scheduler_reentrant_safe,
                       &test_hash_table_put_get,
                       &test_hash_table_string_put_get,
                       &test_hash_table_string_clean_up,
                       &test_hash_table_hash_collision,
                       &test_hash_table_hash_overwrite,
                       &test_hash_table_hash_remove,
                       &test_hash_table_hash_clear_allows_cleanup,
                       &test_hash_table_on_resize_returns_correct_entry,
                       &test_hash_churn,
                       &test_hash_table_foreach,
                       &test_hash_table_iter,
                       &test_hash_table_empty_iter,
                       &test_u64_saturating,
                       &test_u32_saturating,
                       &test_u64_checked,
                       &test_u32_checked,
                       &nospec_index_test,
                       &test_byte_cursor_advance,
                       &test_byte_cursor_advance_nospec,
                       &test_char_split_happy_path,
                       &test_char_split_ends_with_token,
                       &test_char_split_token_not_present,
                       &test_char_split_empty,
                       &test_char_split_adj_tokens,
                       &test_char_split_with_max_splits,
                       &test_char_split_begins_with_token,
                       &test_char_split_output_too_small,
                       &test_buffer_cat,
                       &test_buffer_cat_dest_too_small,
                       &test_buffer_cpy,
                       &test_buffer_cpy_dest_too_small,
                       &test_buffer_cpy_offsets,
                       &test_buffer_cpy_offsets_dest_too_small,
                       &test_secure_zero,
                       &byte_swap_test,
                       &byte_cursor_write_tests,
                       &byte_cursor_read_tests,
                       &byte_cursor_limit_tests,
                       &string_tests,
                       &binary_string_test,
                       &string_compare_test,
                       &test_cpu_count_at_least_works_superficially,
                       &test_realloc_fallback,
                       &test_realloc_fallback_oom,
                       &test_realloc_passthrough_oom,
                       &test_realloc_passthrough,
                       &test_cf_allocator_wrapper,
                       &test_memory_pool_no_overflow,
                       &test_memory_pool_overflow,
                       &test_log_init_clean_up,
                       &test_lru_cache_overflow_static_members,
                       &test_lru_cache_lru_ness_static_members,
                       &test_lru_cache_entries_cleanup,
                       &test_lru_cache_overwrite
                       );
}
