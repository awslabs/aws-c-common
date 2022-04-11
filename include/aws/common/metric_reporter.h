#ifndef AWS_COMMON_METRIC_REPORTER_H
#define AWS_COMMON_METRIC_REPORTER_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

/**
 * Reports CPU usage to the custom metric
 */
AWS_COMMON_API
int aws_get_custom_metric_cpu_usage(double *output);

/**
 * Reports physical memory usage to the custom metric.
 */
AWS_COMMON_API
int aws_get_custom_metric_memory_usage(double *output);

/**
 * Reports process count to the custom metric
 */
AWS_COMMON_API
int aws_get_custom_metric_process_count(double *output);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_METRIC_REPORTER_H */
