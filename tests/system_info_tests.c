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

#include <aws/common/system_info.h>

#include <aws/testing/aws_test_harness.h>

static int s_test_cpu_count_at_least_works_superficially_fn(struct aws_allocator *allocator, void *ctx) {
    (void)allocator;
    (void)ctx;

    size_t processor_count = aws_system_info_processor_count();
    /* I think this is a fairly reasonable assumption given the circumstances
     * (you know this test is part of a program
     * that must be running on at least one core).... */
    ASSERT_TRUE(processor_count > 0);

    return 0;
}

AWS_TEST_CASE(test_cpu_count_at_least_works_superficially, s_test_cpu_count_at_least_works_superficially_fn)

#if defined(_WIN32)
#    include <io.h>
#endif

static int s_test_stack_trace_decoding(struct aws_allocator *allocator, void *ctx) {
    (void)ctx;
    char tmp_filename[] = "backtraceXXXXXX";
    FILE *tmp_file = NULL;

#if defined(_WIN32)
    errno_t tmp_err = _mktemp_s(tmp_filename, sizeof(tmp_filename));
    ASSERT_INT_EQUALS(0, tmp_err);
    errno_t open = fopen_s(&tmp_file, tmp_filename, "w+");
    ASSERT_INT_EQUALS(0, open);
#else
    int tmp_fileno = mkstemp(tmp_filename);
    ASSERT_TRUE(tmp_fileno > -1);
    tmp_file = fdopen(tmp_fileno, "r+");
#endif
    ASSERT_NOT_NULL(tmp_file);

    int line = 0; /* captured on line of aws_backtrace_print call to match call site */
    (void)line;   /* may not be used if debug info is unavailable */
    aws_backtrace_print(tmp_file, (line = __LINE__, NULL)); /* NOLINT */
    fflush(tmp_file);

    fseek(tmp_file, 0L, SEEK_END);
    long file_size = ftell(tmp_file);
    fseek(tmp_file, 0L, SEEK_SET);
    char *buffer = aws_mem_acquire(allocator, file_size + 1);
    ASSERT_NOT_NULL(buffer);
    ASSERT_INT_EQUALS(file_size, fread(buffer, 1, file_size, tmp_file));
    fclose(tmp_file);
    buffer[file_size] = 0;

#if defined(AWS_HAVE_EXECINFO)
    /* ensure that this file/function is found */
    char *file = __FILE__;
    char *next = NULL;
    /* strip path info, just filename will be found */
    while ((next = strstr(file, "/"))) {
        file = next + 1;
    }

    ASSERT_NOT_NULL(strstr(buffer, __func__));
#    if !defined(__APPLE__) /* apple doesn't always find file info */
    /* if this is not a debug build, there may not be symbols, so the test cannot
     * verify if a best effort was made */
#        if defined(DEBUG_BUILD)
    ASSERT_NOT_NULL(strstr(buffer, file));
    /* check for the call site of aws_backtrace_print. Note that line numbers are off by one
     * in both directions depending on compiler, so we check a range around the call site __LINE__
     * The line number can also be ? on old compilers
     */
    char fileline[4096];
    bool found_file_line = false;
    for (int lineno = line - 1; lineno <= line + 1; ++lineno) {
        snprintf(fileline, sizeof(fileline), "%s:%d", file, lineno);
        found_file_line |= strstr(buffer, fileline) != NULL;
    }
    if (!found_file_line) {
        snprintf(fileline, sizeof(fileline), "%s:?", file);
        found_file_line = strstr(buffer, fileline) != NULL;
    }

    ASSERT_TRUE(found_file_line);
#        endif
#    endif /* __APPLE__ */
#endif

    aws_mem_release(allocator, buffer);
    return 0;
}

AWS_TEST_CASE(test_stack_trace_decoding, s_test_stack_trace_decoding);
