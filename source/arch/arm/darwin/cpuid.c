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

#include <aws/common/cpuid.h>

#include <sys/sysctl.h>

bool aws_cpu_has_feature(enum aws_cpu_feature_name feature_name) {
    int64_t ret = 0;
    size_t size = sizeof(ret);

    switch (feature_name) {
        case AWS_CPU_FEATURE_ARM_PMULL:
            if (sysctlbyname("hw.optional.arm.FEAT_PMULL", &ret, &size, NULL, 0) != -1) {
                return ret == 1;
            }
        case AWS_CPU_FEATURE_ARM_CRC:
            if (sysctlbyname("hw.optional.armv8_crc32", &ret, &size, NULL, 0) != -1) {
                return ret == 1;
            }
        case AWS_CPU_FEATURE_ARM_CRYPTO:
            if (sysctlbyname("hw.optional.arm.FEAT_AES", &ret, &size, NULL, 0) != -1) {
                return ret == 1;
            }
        default:
            return false;
    }
}
