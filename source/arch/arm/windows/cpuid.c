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

#include <Windows.h>
#include <aws/common/cpuid.h>

bool aws_cpu_has_feature(enum aws_cpu_feature_name feature_name) {
    switch (feature_name) {
        case AWS_CPU_FEATURE_ARM_CRC:
            return IsProcessorFeaturePresent(PF_ARM_V8_CRC32_INSTRUCTIONS_AVAILABLE) != 0;
        // this is the best we've got on windows as they don't separate PMULL and AES from each other.
        case AWS_CPU_FEATURE_ARM_PMULL:
        case AWS_CPU_FEATURE_ARM_CRYPTO:
            return IsProcessorFeaturePresent(PF_ARM_V8_CRYPTO_INSTRUCTIONS_AVAILABLE) != 0;
        default:
            return false;
    }
}
