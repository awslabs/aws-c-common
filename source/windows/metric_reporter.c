/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/metric_reporter.h>

int aws_get_custom_metric_cpu_usage(double *output)
{
    // Windows is currently not supported.
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}

int aws_get_custom_metric_memory_usage(double *output)
{
    // Windows is currently not supported.
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}

int aws_get_custom_metric_process_count(double *output)
{
    // Windows is currently not supported.
    *output = 0;
    aws_raise_error(AWS_ERROR_PLATFORM_NOT_SUPPORTED);
    return AWS_OP_ERR;
}
