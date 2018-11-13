/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/system_info.h>

#include <assert.h>
#include <unistd.h>

#if defined(HAVE_SYSCONF)
size_t aws_system_info_processor_count(void) {
    long nprocs = sysconf(_SC_NPROCESSORS_ONLN);
    if (AWS_LIKELY(nprocs >= 0)) {
        return (size_t)nprocs;
    }

    assert(0);
    return 0;
}
#else
size_t aws_system_info_processor_count(void) {
#    if defined(AWS_NUM_CPU_CORES)
    assert(AWS_NUM_CPU_CORES > 0);
    return AWS_NUM_CPU_CORES;
#    else
    return 1;
#    endif
}
#endif
