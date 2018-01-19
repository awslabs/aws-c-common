/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 * http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

#include <aws/common/clock.h>
#include <mach/mach_time.h>
#include <mach/mach_host.h>
#include <mach/clock.h>
#include <mach/mach_port.h>

static mach_timebase_info_data_t timebase_info;

int aws_high_res_clock_get_ticks(uint64_t *timestamp) {
    uint64_t temp_time = mach_absolute_time();

    if(timebase_info.denom == 0) {
        mach_timebase_info(&timebase_info);
    }

    *timestamp = temp_time * timebase_info.numer / timebase_info.denom;
    return AWS_OP_SUCCESS;
}

int aws_sys_clock_get_ticks(uint64_t *timestamp) {
    clock_serv_t clock;
    mach_timespec_t timespec;
    host_get_clock_service(mach_host_self(), CALENDAR_CLOCK, &clock);
    clock_get_time(clock, &timespec);
    /*I've profiled this, can't find a noticable enough impact to worry about it (it's a sys clock after all) */
    mach_port_deallocate(mach_host_self(), clock);
    *timestamp = (uint64_t)((timespec.tv_sec * 1000000000) + timespec.tv_nsec);
    return AWS_OP_SUCCESS;
}

