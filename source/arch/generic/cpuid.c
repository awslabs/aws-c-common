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

/*
 * MSVC wants us to use the non-portable _dupenv_s instead; since we need
 * to remain portable, tell MSVC to suppress this warning.
 */

#include <aws/common/cpuid.h>

bool aws_cpu_has_feature(enum aws_cpu_feature_name feature_name) {
    return false;
}