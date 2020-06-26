/* NOLINTNEXTLINE(llvm-header-guard) */
#ifndef AWS_COMMON_TEST_LOGGER_H
#define AWS_COMMON_TEST_LOGGER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/logging.h>

#include <aws/common/byte_buf.h>

/**
 * The test logger is a simple forwarding logger that just records what was passed to it.
 * We provide an extraction function for easy test validation.
 */
struct test_logger_impl {
    enum aws_log_level level;
    struct aws_byte_buf log_buffer;
    size_t max_size;
};

/**
 * Given a pointer to a logger, initializes it as a test logger using the supplied log level.
 * max_size of 0 is unlimited
 */
int test_logger_init(
    struct aws_logger *logger,
    struct aws_allocator *allocator,
    enum aws_log_level level,
    size_t max_size);

/**
 * Extracts logged content from a test logger.
 */
int test_logger_get_contents(struct aws_logger *logger, char *buffer, size_t max_length);

#endif /* AWS_COMMON_TEST_LOGGER_H */
