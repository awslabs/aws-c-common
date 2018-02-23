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

#include <stdio.h>
#include <assert.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#ifndef AWS_UNSTABLE_TESTING_API
#error The AWS Test Fixture is designed only for use by AWS owned libraries for the AWS C99 SDK. You are welcome to use it,   \
but you should be aware we make no promises on the stability of this API.  To enable use of the aws test fixtures, set \
the AWS_UNSTABLE_TESTING_API compiler flag
#endif

struct memory_test_config {
    void *(*mem_acquire)(struct aws_allocator *config, size_t size);
    void (*mem_release)(struct aws_allocator *config, void *ptr);
    size_t allocated;
    size_t freed;
};

struct memory_test_tracker {
    size_t size;
    void *blob;
};

static void *mem_acquire_malloc(struct aws_allocator *config, size_t size) {
    struct memory_test_config *test_config = (struct memory_test_config *)config;
    test_config->allocated += size;
    struct memory_test_tracker *memory =
        (struct memory_test_tracker *)malloc(size + sizeof(struct memory_test_tracker));
    memory->size = size;
    memory->blob = (uint8_t *)memory + sizeof(struct memory_test_tracker);
    return memory->blob;
}

static void mem_release_free(struct aws_allocator *config, void *ptr) {
    struct memory_test_config *test_config = (struct memory_test_config *)config;

    struct memory_test_tracker *memory =
        (struct memory_test_tracker *)((uint8_t *)ptr - sizeof(struct memory_test_tracker));
    test_config->freed += memory->size;

    free(memory);
}

#define AWS_MEMORY_TEST_CONFIG                                                                                         \
    { .mem_acquire = mem_acquire_malloc, .mem_release = mem_release_free, .allocated = 0, .freed = 0 }

/** Prints a message to stdout using printf format that appends the function, file and line number. */
static void cunit_failure_message(const char *function, const char *file, int line, const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    char buffer1[4096];
    vsnprintf(buffer1, sizeof(buffer1), format, ap);
    buffer1[sizeof(buffer1) - 1] = 0;
    va_end(ap);

    char buffer2[4096];
    snprintf(buffer2, sizeof(buffer2), " [%s():%s@#%d]", function, file, line);
    buffer2[sizeof(buffer2) - 1] = 0;

    fprintf(stderr, "%s%s\n", buffer1, buffer2);
}

static int total_failures;

#define SUCCESS 0
#define FAILURE -1

#define RETURN_SUCCESS(format, ...)                                                                                    \
    do {                                                                                                               \
        printf(format, ##__VA_ARGS__);                                                                                 \
        printf("\n");                                                                                                  \
        return SUCCESS;                                                                                                \
    } while (0)
#define FAIL(format, ...)                                                                                              \
    do {                                                                                                               \
        cunit_failure_message(__FUNCTION__, __FILE__, __LINE__, "***FAILURE*** " format, ##__VA_ARGS__);               \
        total_failures++;                                                                                              \
        return FAILURE;                                                                                                \
    } while (0)
#define ASSERT_TRUE(condition, format, ...)                                                                            \
    do {                                                                                                               \
        if (!(condition)) {                                                                                            \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_FALSE(condition, format, ...)                                                                           \
    do {                                                                                                               \
        if (condition) {                                                                                               \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)

#define ASSERT_SUCCESS(condition, format, ...)                                                                         \
    do {                                                                                                               \
        if (condition != AWS_OP_SUCCESS) {                                                                             \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_FAILS(condition, format, ...)                                                                           \
    do {                                                                                                               \
        if (condition != AWS_OP_ERR) {                                                                                 \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_ERROR(error, condition, format, ...)                                                                    \
    do {                                                                                                               \
        if (condition != -1) {                                                                                         \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
        if (aws_last_error() != error) {                                                                               \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_NULL(ptr, format, ...)                                                                                  \
    do {                                                                                                               \
        if (ptr) {                                                                                                     \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_NOT_NULL(ptr, format, ...)                                                                              \
    do {                                                                                                               \
        if (!ptr) {                                                                                                    \
            FAIL(format, ##__VA_ARGS__);                                                                               \
        }                                                                                                              \
    } while (0)
#define ASSERT_INT_EQUALS(expected, got, message, ...)                                                                 \
    do {                                                                                                               \
        long long a = (long long)(expected);                                                                           \
        long long b = (long long)(got);                                                                                \
        if (a != b) {                                                                                                  \
            FAIL("Expected:%lld got:%lld - " message, a, b, ##__VA_ARGS__);                                            \
        }                                                                                                              \
    } while (0)
#define ASSERT_PTR_EQUALS(expected, got, message, ...)                                                                 \
    do {                                                                                                               \
        void *a = (void *)(expected);                                                                                  \
        void *b = (void *)(got);                                                                                       \
        if (a != b) {                                                                                                  \
            FAIL("Expected:%lld got:%lld - " message, a, b, ##__VA_ARGS__);                                            \
        }                                                                                                              \
    } while (0)
#define ASSERT_STR_EQUALS(expected, got, message, ...)                                                                 \
    do {                                                                                                               \
        if (strcmp(expected, got)) {                                                                                   \
            FAIL("Expected:%x got:%x - " message, expected, got, ##__VA_ARGS__);                                       \
        }                                                                                                              \
    } while (0)
#define ASSERT_BYTE_HEX_EQUALS(expected, got, message, ...)                                                            \
    do {                                                                                                               \
        uint8_t a = (uint8_t)(expected);                                                                               \
        uint8_t b = (uint8_t)(got);                                                                                    \
        if (a != b) {                                                                                                  \
            FAIL("Expected:%x got:%x - " message, a, b, ##__VA_ARGS__);                                                \
        }                                                                                                              \
    } while (0)
#define ASSERT_HEX_EQUALS(expected, got, message, ...)                                                                 \
    do {                                                                                                               \
        long long a = (long long)(expected);                                                                           \
        long long b = (long long)(got);                                                                                \
        if (a != b) {                                                                                                  \
            FAIL("Expected:%llX got:%llX - " message, a, b, ##__VA_ARGS__);                                            \
        }                                                                                                              \
    } while (0)
#define ASSERT_BIN_ARRAYS_EQUALS(expected, expected_size, got, got_size, message, ...)                                 \
    for (size_t i = 0; i < expected_size; ++i) {                                                                       \
        if (expected[i] != got[i]) {                                                                                   \
            FAIL("Expected:%02x got:%02x - " message, expected[i], got[i], ##__VA_ARGS__);                             \
        }                                                                                                              \
    }

typedef void (*aws_test_before)(struct aws_allocator *allocator, void *ctx);
typedef int (*aws_test_run)(struct aws_allocator *allocator, void *ctx);
typedef void (*aws_test_after)(struct aws_allocator *allocator, void *ctx);

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
    static struct aws_test_harness name = {.on_before = NULL,                                                          \
                                           .run = fn,                                                                  \
                                           .on_after = NULL,                                                           \
                                           .ctx = NULL,                                                                \
                                           .config = AWS_MEMORY_TEST_CONFIG,                                           \
                                           .test_name = #name,                                                         \
                                           .suppress_memcheck = s};

#define AWS_TEST_CASE_FIXTURE_SUPPRESSION(name, b, fn, af, c, s)                                                       \
    static struct aws_test_harness name = {.on_before = b,                                                             \
                                           .run = fn,                                                                  \
                                           .on_after = af,                                                             \
                                           .ctx = NULL,                                                                \
                                           .config = AWS_MEMORY_TEST_CONFIG,                                           \
                                           .test_name = #name,                                                         \
                                           .suppress_memcheck = s};

#define AWS_TEST_CASE(name, fn) AWS_TEST_CASE_SUPRESSION(name, fn, 0)
#define AWS_TEST_CASE_FIXTURE(name, b, fn, af, c) AWS_TEST_CASE_FIXTURE_SUPPRESSION(name, b, fn, af, c, 0)

static int aws_run_test_case(struct aws_test_harness *harness) {
    assert(harness->run);

    if (harness->on_before) {
        harness->on_before((struct aws_allocator *)&harness->config, harness->ctx);
    }

    int ret_val = harness->run((struct aws_allocator *)&harness->config, harness->ctx);

    if (harness->on_after) {
        harness->on_after((struct aws_allocator *)&harness->config, harness->ctx);
    }

    if (!ret_val) {
        if (!harness->suppress_memcheck) {
            ASSERT_INT_EQUALS(harness->config.allocated, harness->config.freed,
                              "%s [ \033[31mFAILED\033[0m ]"
                              "Memory Leak Detected %d bytes were allocated, "
                              "but only %d were freed.",
                              harness->test_name, harness->config.allocated, harness->config.freed);
        }

        RETURN_SUCCESS("%s [ \033[32mOK\033[0m ]", harness->test_name);
    }

    FAIL("%s [ \033[31mFAILED\033[0m ]", harness->test_name);
}

#define AWS_RUN_TEST_CASES(...)                                                                                        \
    struct aws_test_harness *tests[] = {__VA_ARGS__};                                                                  \
    int ret_val = 0;                                                                                                   \
                                                                                                                       \
    const char *test_name = NULL;                                                                                      \
    if (argc >= 2) {                                                                                                   \
        test_name = argv[1];                                                                                           \
    }                                                                                                                  \
                                                                                                                       \
    size_t test_count = sizeof(tests) / sizeof(struct aws_test_harness *);                                             \
    if (test_name) {                                                                                                   \
        for (size_t i = 0; i < test_count; ++i) {                                                                      \
            if (!strcmp(test_name, tests[i]->test_name)) {                                                             \
                return aws_run_test_case(tests[i]);                                                                    \
            }                                                                                                          \
        }                                                                                                              \
        return -1;                                                                                                     \
    }                                                                                                                  \
    else {                                                                                                             \
        for (size_t i = 0; i < test_count; ++i) {                                                                      \
            ret_val |= aws_run_test_case(tests[i]);                                                                    \
        }                                                                                                              \
    }                                                                                                                  \
                                                                                                                       \
    fflush(stdout);                                                                                                    \
    fflush(stderr);                                                                                                    \
    return ret_val;

#endif /* AWS_TEST_HARNESS_H _*/
