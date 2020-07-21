/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define AWS_STATIC_LOG_LEVEL 2

#include "logging_test_utilities.h"

/**
 * A log testing callback that makes a LOGF_ call for each level.
 *
 * Because AWS_STATIC_LOG_LEVEL is 2 (ERROR) in this translation unit, we expect all but two
 * of the log calls to be removed at compile time.
 *
 * So even though our test sets the dynamic level to TRACE, only the FATAL and ERROR log calls will
 * be recorded.
 */
DECLARE_LOGF_ALL_LEVELS_FUNCTION(s_logf_all_levels_error_cutoff)

TEST_LEVEL_FILTER(AWS_LL_TRACE, "12", s_logf_all_levels_error_cutoff)
