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

#include <aws/common/array_list.h>
#include <aws/common/hash_table.h>
#include <aws/common/string.h>
#include <aws/testing/aws_test_harness.h>

/* Defines known_test_case_names */
#include "test_crosscheck.inl"

struct aws_test_registration *aws_test_registry_head = NULL;

static void noop_destroy(void *ignored) {
    (void)ignored;
}

AWS_TEST_CASE(test_crosscheck, s_test_crosscheck_fn)
static int s_test_crosscheck_fn(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;

    bool ok = true;
    struct aws_hash_table known_tests;
    struct aws_array_list expected_tests;

    if (aws_test_registry_head == NULL) {
        fprintf(stderr, "Test crosscheck skipped - no tests registered in source\n");
        return 0;
    }

    ASSERT_SUCCESS(aws_hash_table_init(
        &known_tests, allocator, 512, aws_hash_string, aws_string_eq, aws_string_destroy, noop_destroy));
    ASSERT_SUCCESS(aws_array_list_init_dynamic(&expected_tests, allocator, 512, sizeof(struct aws_byte_cursor)));

    for (struct aws_test_registration *current = aws_test_registry_head; current; current = current->next) {
        struct aws_string *name = aws_string_new_from_c_str(allocator, current->test_name);
        int was_created;

        ASSERT_NOT_NULL(name);
        ASSERT_SUCCESS(aws_hash_table_put(&known_tests, name, name, &was_created));

        if (!was_created) {
            ok = false;
            fprintf(stderr, "Duplicate test in source: \"%s\"\n", current->test_name);
        }
    }

    struct aws_byte_buf to_split = aws_byte_buf_from_c_str(known_test_case_names);

    ASSERT_SUCCESS(aws_byte_buf_split_on_char(&to_split, ';', &expected_tests));

    size_t n_tests = aws_array_list_length(&expected_tests);

    for (size_t i = 0; i < n_tests; i++) {
        struct aws_byte_cursor cursor;
        ASSERT_SUCCESS(aws_array_list_get_at(&expected_tests, &cursor, i));

        struct aws_string *name = aws_string_new_from_array(allocator, cursor.ptr, cursor.len);
        int was_present;
        ASSERT_SUCCESS(aws_hash_table_remove(&known_tests, name, NULL, &was_present));

        if (!was_present) {
            ok = false;
            fprintf(
                stderr,
                "Test was present in CMakeList.txt but not in source (or was duplicate): \"%s\"\n",
                aws_string_bytes(name));
        }
        aws_string_destroy(name);
    }

    for (struct aws_hash_iter iter = aws_hash_iter_begin(&known_tests); !aws_hash_iter_done(&iter);
         aws_hash_iter_next(&iter)) {
        ok = false;
        fprintf(stderr, "Test was in source but not in CMakeLists.txt: \"%s\"\n", aws_string_bytes(iter.element.key));
    }

    aws_hash_table_clean_up(&known_tests);
    aws_array_list_clean_up(&expected_tests);

    return !ok;
}
