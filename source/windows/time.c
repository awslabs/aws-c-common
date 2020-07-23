/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/time.h>

time_t aws_timegm(struct tm *const t) {
    return _mkgmtime(t);
}

void aws_localtime(time_t time, struct tm *t) {
    localtime_s(t, &time);
}

void aws_gmtime(time_t time, struct tm *t) {
    gmtime_s(t, &time);
}
