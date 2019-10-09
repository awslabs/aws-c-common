#ifndef AWS_COMMON_STATISTICS_H
#define AWS_COMMON_STATISTICS_H

/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <aws/common/package.h>

#include <stdint.h>

struct aws_array_list;

typedef uint32_t aws_crt_statistics_category_t;

#define AWS_CRT_STATISTICS_CATEGORY_STRIDE_BITS 8
#define AWS_CRT_STATISTICS_CATEGORY_STRIDE (1U << AWS_CRT_STATISTICS_CATEGORY_STRIDE_BITS)

enum aws_crt_common_statistics_category {
    AWSCRT_STAT_CAT_INVALID = AWS_C_COMMON_PACKAGE_ID * AWS_CRT_STATISTICS_CATEGORY_STRIDE
};

struct aws_crt_statistics_base {
    aws_crt_statistics_category_t category;
};

struct aws_crt_statistics_sample_interval {
    uint64_t begin_time_ms;
    uint64_t end_time_ms;
};

struct aws_crt_statistics_handler;

typedef void(aws_crt_statistics_handler_process_statistics_fn)(
    struct aws_crt_statistics_handler *,
    struct aws_crt_statistics_sample_interval *,
    struct aws_array_list *);

typedef void(aws_crt_statistics_handler_cleanup_fn)(struct aws_crt_statistics_handler *);
typedef uint64_t(aws_crt_statistics_handler_get_report_interval_ms_fn)(struct aws_crt_statistics_handler *);

struct aws_crt_statistics_handler_vtable {
    aws_crt_statistics_handler_process_statistics_fn *process_statistics;
    aws_crt_statistics_handler_cleanup_fn *cleanup;
    aws_crt_statistics_handler_get_report_interval_ms_fn *get_report_interval_ms;
};

struct aws_crt_statistics_handler {
    struct aws_crt_statistics_handler_vtable *vtable;
    struct aws_allocator *allocator;
    void *impl;
};

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_crt_statistics_handler_destroy(struct aws_crt_statistics_handler *handler);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_STATISTICS_H */
