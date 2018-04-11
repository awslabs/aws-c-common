#ifndef AWS_TEST_HARNESS_H_
#define AWS_TEST_HARNESS_H_
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

#include <aws/common/common.h>
#include <aws/common/error.h>
#include <aws/common/mutex.h>

#include <stdio.h>
#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#ifndef AWS_UNSTABLE_TESTING_API
#error                                                                                                                 \
The AWS Test Fixture is designed only for use by AWS owned libraries for the AWS C99 SDK. You are welcome to use it,   \
but you should be aware we make no promises on the stability of this API.  To enable use of the aws test fixtures, set \
the AWS_UNSTABLE_TESTING_API compiler flag
#endif

#ifndef AWS_TESTING_REPORT_FD
#define AWS_TESTING_REPORT_FD stderr
#endif

struct memory_test_config {
    void *(*mem_acquire)(struct aws_allocator *config, size_t size);
    void(*mem_release)(struct aws_allocator *config, void *ptr);
    size_t allocated;
    size_t freed;
    struct aws_mutex mutex;
};

struct memory_test_tracker {
    size_t size;
    void *blob;
};

static void *mem_acquire_malloc(struct aws_allocator *config, size_t size) {
    struct memory_test_config *test_config = (struct memory_test_config *)config;

    aws_mutex_lock(&test_config->mutex);
    test_config->allocated += size;
    struct memory_test_tracker *memory = (struct memory_test_tracker *) malloc(size + sizeof(struct memory_test_tracker));
    memory->size = size;
    memory->blob = (uint8_t *)memory + sizeof(struct memory_test_tracker);
    aws_mutex_unlock(&test_config->mutex);
    return memory->blob;
}

static void mem_release_free(struct aws_allocator *config, void *ptr) {
    struct memory_test_config *test_config = (struct memory_test_config *)config;

    struct memory_test_tracker *memory = (struct memory_test_tracker *) ((uint8_t *)ptr - sizeof(struct memory_test_tracker));
    aws_mutex_lock(&test_config->mutex);
    test_config->freed += memory->size;
    aws_mutex_unlock(&test_config->mutex);
    free(memory);
}

#define AWS_MEMORY_TEST_CONFIG                                                                                         \
  {                                                                                                                    \
        .mem_acquire = mem_acquire_malloc,                                                                             \
        .mem_release = mem_release_free,                                                                               \
        .allocated = 0,                                                                                                \
        .freed = 0,                                                                                                    \
  }                                                                                                                    \

/** Prints a message to stdout using printf format that appends the function, file and line number.
  * If format is null, returns 0 without printing anything; otherwise returns 1.
  */
static int cunit_failure_message0(const char *prefix, const char *function, const char *file, int line, const char *format, ...) {
    if (!format) return 0;

    fprintf(AWS_TESTING_REPORT_FD, "%s", prefix);

    va_list ap;
    va_start(ap, format);
    vfprintf(AWS_TESTING_REPORT_FD, format, ap);
    va_end(ap);

    fprintf(AWS_TESTING_REPORT_FD, " [%s():%s@#%d]\n", function, file, line);

    return 1;
}

#define FAIL_PREFIX "***FAILURE*** "
#define cunit_failure_message(func, file, line, format, ...) \
    cunit_failure_message0(FAIL_PREFIX, func, file, line, format, # __VA_ARGS__)

static int total_failures;

#define SUCCESS 0
#define FAILURE -1

#define RETURN_SUCCESS(format, ...) do { printf(format, ## __VA_ARGS__); printf("\n"); return SUCCESS; } while (0)
#define PRINT_FAIL_INTERNAL(...) \
    cunit_failure_message(__FUNCTION__, __FILE__, __LINE__, ## __VA_ARGS__, (const char *)NULL)

#define PRINT_FAIL_INTERNAL0(...) \
    cunit_failure_message0("", __FUNCTION__, __FILE__, __LINE__, ## __VA_ARGS__, (const char *)NULL)

#define POSTFAIL_INTERNAL() do {\
    total_failures++; \
    return FAILURE; \
} while (0)

#define FAIL(format, ...)  \
    do { PRINT_FAIL_INTERNAL(format, ## __VA_ARGS__); POSTFAIL_INTERNAL(); } while (0)


#define ASSERT_TRUE(condition, ...) \
    do { \
        if(!(condition)) { \
            if (!PRINT_FAIL_INTERNAL(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL("Expected condition to be true: " #condition); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while(0)

#define ASSERT_FALSE(condition, ...) \
    do { \
        if((condition)) { \
            if (!PRINT_FAIL_INTERNAL(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL("Expected condition to be false: " #condition); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_SUCCESS(condition, ...) \
    do { \
        int assert_rv = (condition); \
        if (assert_rv != AWS_OP_SUCCESS) { \
            if (!PRINT_FAIL_INTERNAL(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL("Expected success at %s; got return value %d with last error 0x%04x\n", \
                    #condition, assert_rv, aws_last_error()); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_FAILS(condition, ...) \
    do { \
        int assert_rv = (condition); \
        if (assert_rv != AWS_OP_ERR) { \
            if (!PRINT_FAIL_INTERNAL(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL("Expected failure at %s; got return value %d with last error 0x%04x\n", \
                    #condition, assert_rv, aws_last_error()); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_ERROR(error, condition, ...) \
    do { \
        int assert_rv = (condition); \
        int assert_err = aws_last_error(); \
        int assert_err_expect = (error); \
        if (assert_rv != AWS_OP_ERR) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sExpected error but no error occurred; rv=%d, aws_last_error=%04x (expected %04x): ", FAIL_PREFIX, assert_rv, assert_err, assert_err_expect); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("%s", #condition); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
        if (assert_err != assert_err_expect) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sIncorrect error code; aws_last_error=%04x (expected %04x): ", FAIL_PREFIX, assert_err, assert_err_expect); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("%s", #condition); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_NULL(ptr, ...) \
    do { \
        /* XXX: Some tests use ASSERT_NULL on ints... */ \
        void *assert_p = (void *)(uintptr_t)(ptr); \
        if (assert_p) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sExpected null but got %p: ", FAIL_PREFIX, assert_p); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("%s", #ptr); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_NOT_NULL(ptr, ...) \
    do { \
        /* XXX: Some tests use ASSERT_NULL on ints... */ \
        void *assert_p = (void *)(uintptr_t)(ptr); \
        if (!assert_p) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sExpected non-null but got null: ", FAIL_PREFIX); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("%s", #ptr); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_TYP_EQUALS(type, formatarg, expected, got, ...) \
    do { \
        type assert_expected = (type)(expected); \
        type assert_actual   = (type)(got); \
        if (assert_expected != assert_actual) { \
            fprintf(AWS_TESTING_REPORT_FD, "%s" formatarg " != " formatarg ": ", FAIL_PREFIX, assert_expected, assert_actual); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("%s != %s", #expected, #got); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while (0)

#define ASSERT_INT_EQUALS(expected, got, ...) ASSERT_TYP_EQUALS(long long, "%lld", expected, got, __VA_ARGS__)
#define ASSERT_UINT_EQUALS(expected, got, ...) ASSERT_TYP_EQUALS(unsigned long long, "%llu", expected, got, __VA_ARGS__)
#define ASSERT_PTR_EQUALS(expected, got, ...) ASSERT_TYP_EQUALS(void *, "%p", expected, got, __VA_ARGS__)
/* note that uint8_t is promoted to unsigned int in varargs, so %02x is an acceptable format string */
#define ASSERT_BYTE_HEX_EQUALS(expected, got, ...) ASSERT_TYP_EQUALS(uint8_t, "%02X", expected, got, __VA_ARGS__)
#define ASSERT_HEX_EQUALS(expected, got, ...) ASSERT_TYP_EQUALS(unsigned long long, "%llX", expected, got, __VA_ARGS__)

#define ASSERT_STR_EQUALS(expected, got, ...) \
    do { \
        const char *assert_expected = (expected); \
        const char *assert_got = (got); \
        if (strcmp(assert_expected, assert_got)) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sExpected: \"%s\"; got: \"%s\": ", FAIL_PREFIX, assert_expected, assert_got); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("ASSERT_STR_EQUALS(%s, %s)", #expected, #got); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while(0)

#define ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, got, got_size, ...) \
    do { \
        const uint8_t *assert_ex_p = (const uint8_t *)(expected); \
        size_t assert_ex_s = (expected_size); \
        const uint8_t *assert_got_p = (const uint8_t *)(got); \
        size_t assert_got_s = (got_size); \
        if (assert_ex_s != assert_got_s) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sSize mismatch: %zu != %zu: ", FAIL_PREFIX, assert_ex_s, assert_got_s); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("ASSERT_BIN_ARRAYS_EQUALS(%s, %s, %s, %s)", \
                    #expected, #expected_size, #got, #got_size); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
        if (memcmp(assert_ex_p, assert_got_p, assert_got_s)) { \
            fprintf(AWS_TESTING_REPORT_FD, "%sData mismatch: ", FAIL_PREFIX); \
            if (!PRINT_FAIL_INTERNAL0(__VA_ARGS__)) { \
                PRINT_FAIL_INTERNAL0("ASSERT_BIN_ARRAYS_EQUALS(%s, %s, %s, %s)", \
                    #expected, #expected_size, #got, #got_size); \
            } \
            POSTFAIL_INTERNAL(); \
        } \
    } while(0)
        
typedef void(*aws_test_before)(struct aws_allocator *allocator, void *ctx);
typedef int(*aws_test_run)(struct aws_allocator *allocator, void *ctx);
typedef void(*aws_test_after)(struct aws_allocator *allocator, void *ctx);

struct aws_test_harness {
    aws_test_before on_before;
    aws_test_run run;
    aws_test_after on_after;
    struct memory_test_config config;
    void *ctx;
    const char *test_name;
    int suppress_memcheck;
};

#define AWS_TEST_CASE_SUPRESSION(name, fn, s)                                                                          \
    static int fn(struct aws_allocator *allocator, void *ctx);                                                         \
    static struct aws_test_harness name = { .on_before = NULL, .run = fn, .on_after = NULL,                            \
         .ctx = NULL, .config = AWS_MEMORY_TEST_CONFIG, .test_name = #name, .suppress_memcheck = s };                  \

#define AWS_TEST_CASE_FIXTURE_SUPPRESSION(name, b, fn, af, c, s)                                                       \
    static void b(struct aws_allocator *allocator, void *ctx);                                                         \
    static int fn(struct aws_allocator *allocator, void *ctx);                                                         \
    static void af(struct aws_allocator *allocator, void *ctx);                                                        \
    static struct aws_test_harness name = { .on_before = b, .run = fn, .on_after = af,                                 \
        .ctx = NULL, .config = AWS_MEMORY_TEST_CONFIG, .test_name = #name, .suppress_memcheck = s };                   \

#define AWS_TEST_CASE(name, fn) AWS_TEST_CASE_SUPRESSION(name, fn, 0)
#define AWS_TEST_CASE_FIXTURE(name, b, fn, af, c) AWS_TEST_CASE_FIXTURE_SUPPRESSION(name, b, fn, af, c, 0)

static int aws_run_test_case(struct aws_test_harness *harness) {
    assert(harness->run);
    harness->config.mutex = aws_mutex_static_init();

    if(harness->on_before) {
        harness->on_before((struct aws_allocator *)&harness->config, harness->ctx);
    }

    int ret_val = harness->run((struct aws_allocator *)&harness->config, harness->ctx);

    if(harness->on_after) {
        harness->on_after((struct aws_allocator *)&harness->config, harness->ctx);
    }

    if(!ret_val) {
        if (!harness->suppress_memcheck) {
            ASSERT_INT_EQUALS(harness->config.allocated, harness->config.freed, "%s [ \033[31mFAILED\033[0m ]"
                "Memory Leak Detected %d bytes were allocated, "
                "but only %d were freed.", harness->test_name, harness->config.allocated, harness->config.freed);
        }

        RETURN_SUCCESS("%s [ \033[32mOK\033[0m ]", harness->test_name);
    }


    FAIL("%s [ \033[31mFAILED\033[0m ]", harness->test_name);
}

#define AWS_RUN_TEST_CASES(...)                                                                                        \
    struct aws_test_harness *tests[] = { __VA_ARGS__ };                                                                \
    int ret_val = 0;                                                                                                   \
                                                                                                                       \
    const char *test_name = NULL;                                                                                      \
    if (argc >= 2) {                                                                                                   \
        test_name = argv[1];                                                                                           \
    }                                                                                                                  \
                                                                                                                       \
    size_t test_count = sizeof(tests) / sizeof(struct aws_test_harness*);                                              \
    if(test_name) {                                                                                                    \
        ret_val = -1;                                                                                                  \
        for(size_t i = 0; i < test_count; ++i) {                                                                       \
            if(!strcmp(test_name, tests[i]->test_name)) {                                                              \
                ret_val = aws_run_test_case(tests[i]);                                                                 \
                break;                                                                                                 \
            }                                                                                                          \
        }                                                                                                              \
    }                                                                                                                  \
    else {                                                                                                             \
        for(size_t i = 0; i < test_count; ++i) {                                                                       \
            ret_val |= aws_run_test_case(tests[i]);                                                                    \
        }                                                                                                              \
    }                                                                                                                  \
                                                                                                                       \
    fflush(stdout);                                                                                                    \
    fflush(AWS_TESTING_REPORT_FD);                                                                                     \
    return ret_val;                                                                                                    \

#endif /* AWS_TEST_HARNESS_H _*/
