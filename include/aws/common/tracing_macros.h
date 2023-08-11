#ifndef AWS_TRACING_MACROS_H
#define AWS_TRACING_MACROS_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

/**
 * THIS IS NOT INTENDED FOR PUBLIC USE.
 */
#ifdef AWS_ENABLE_TRACING
#    include "ittnotify.h"
extern __itt_domain *s3_domain;
#else
#    define INTEL_NO_ITTNOTIFY_API
#    include "ittnotify.h"
#endif

#endif /* AWS_TRACING_MACROS_H */
