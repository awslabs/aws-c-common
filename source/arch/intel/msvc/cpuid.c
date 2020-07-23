/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/cpuid.h>

#include <intrin.h>

void aws_run_cpuid(uint32_t eax, uint32_t ecx, uint32_t *abcd) {
    __cpuidex((int32_t *)abcd, eax, ecx);
}
