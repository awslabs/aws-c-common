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

#include <aws/common/clock.h>

static struct aws_clock_system_vtable s_default_vtable = {
    .system_clock = aws_sys_clock_get_ticks_platform,
    .high_res_clock = aws_high_res_clock_get_ticks_platform,
};

static struct aws_clock_system_vtable *s_clock_vtable = &s_default_vtable;

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    if (s_clock_vtable->high_res_clock) {
        return s_clock_vtable->high_res_clock(timestamp);
    }

    return aws_raise_error(AWS_ERROR_UNIMPLEMENTED);
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
    if (s_clock_vtable->system_clock) {
        return s_clock_vtable->system_clock(timestamp);
    }

    return aws_raise_error(AWS_ERROR_UNIMPLEMENTED);
}

void aws_clock_set_system_vtable(struct aws_clock_system_vtable *vtable) {
    if (vtable != NULL) {
        s_clock_vtable = vtable;
    }
}
