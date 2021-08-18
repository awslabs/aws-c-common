/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#define AWS_STATIC_LOG_LEVEL 6

#include "logging_test_utilities.h"

/**
 * A log testing callback that makes a LOGF_ call for each level.
 *
 * Because AWS_STATIC_LOG_LEVEL is 6 (TRACE) in this translation unit, we do not expect any
 * of the log calls to be removed at compile time.
 *
 */
DECLARE_LOGF_ALL_LEVELS_FUNCTION(s_logf_all_levels_trace_cutoff)

TEST_LEVEL_FILTER(AWS_LL_TRACE, "123456", s_logf_all_levels_trace_cutoff)
