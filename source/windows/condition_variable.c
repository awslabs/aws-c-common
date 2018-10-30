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

#include <aws/common/condition_variable.h>

#include <aws/common/clock.h>
#include <aws/common/mutex.h>

#include <Windows.h>

/* Ensure our condition variable and Windows' condition variables are the same size */
AWS_STATIC_ASSERT(sizeof(CONDITION_VARIABLE) == sizeof(struct aws_condition_variable));

#define AWSCV_TO_WINDOWS(pCV) (PCONDITION_VARIABLE) pCV

int aws_condition_variable_init(struct aws_condition_variable *condition_variable) {

    InitializeConditionVariable(AWSCV_TO_WINDOWS(condition_variable));
    return AWS_OP_SUCCESS;
}

void aws_condition_variable_clean_up(struct aws_condition_variable *condition_variable) {
    (void)condition_variable;
    /* no op */
}

int aws_condition_variable_notify_one(struct aws_condition_variable *condition_variable) {

    WakeConditionVariable(AWSCV_TO_WINDOWS(condition_variable));
    return AWS_OP_SUCCESS;
}

int aws_condition_variable_notify_all(struct aws_condition_variable *condition_variable) {

    WakeAllConditionVariable(AWSCV_TO_WINDOWS(condition_variable));
    return AWS_OP_SUCCESS;
}

int aws_condition_variable_wait(struct aws_condition_variable *condition_variable, struct aws_mutex *mutex) {

    if (SleepConditionVariableSRW(AWSCV_TO_WINDOWS(condition_variable), AWSMUTEX_TO_WINDOWS(mutex), INFINITE, 0)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_COND_VARIABLE_ERROR_UNKNOWN);
}

int aws_condition_variable_wait_for(
    struct aws_condition_variable *condition_variable,
    struct aws_mutex *mutex,
    int64_t time_to_wait) {

    DWORD time_ms = (DWORD)aws_timestamp_convert(time_to_wait, AWS_TIMESTAMP_NANOS, AWS_TIMESTAMP_MILLIS, NULL);

    if (SleepConditionVariableSRW(AWSCV_TO_WINDOWS(condition_variable), AWSMUTEX_TO_WINDOWS(mutex), time_ms, 0)) {
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_COND_VARIABLE_TIMED_OUT);
}
