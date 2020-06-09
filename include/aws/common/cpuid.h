#ifndef AWS_COMMON_CPUID_H
#define AWS_COMMON_CPUID_H
/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

enum aws_cpu_feature_name {
    AWS_CPU_FEATURE_CLMUL,
    AWS_CPU_FEATURE_SSE_4_1,
    AWS_CPU_FEATURE_SSE_4_2,
    AWS_CPU_FEATURE_AVX2,
    AWS_CPU_FEATURE_COUNT,
};

AWS_EXTERN_C_BEGIN

/**
 * Returns true if a cpu feature is supported, false otherwise.
 */
AWS_COMMON_API bool aws_cpu_has_feature(enum aws_cpu_feature_name feature_name);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_CPUID_H */
