/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define AWS_STATIC_LOG_LEVEL 0

#include "logging_test_utilities.h"

/**
 * A log testing callback that makes a LOGF_ call for each level.
 *
 * Because AWS_STATIC_LOG_LEVEL is 0 (NONE) in this translation unit, we expect all of the log
 * calls to be removed at compile time.
 *
 * So even though our test sets the dynamic level to TRACE, nothing will
 * be recorded.
 */
DECLARE_LOGF_ALL_LEVELS_FUNCTION(s_logf_all_levels_none_cutoff)

TEST_LEVEL_FILTER(AWS_LL_TRACE, "", s_logf_all_levels_none_cutoff)
