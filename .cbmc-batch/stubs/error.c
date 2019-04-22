/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

static AWS_THREAD_LOCAL int tl_last_error = 0;

/**
 * It overrides the original aws_raise_error_private implementation, to avoid
 * error handler functions (unnecessary for the verification process).
 */
void aws_raise_error_private(int err) {
    tl_last_error = err;
}

/**
 * It overrides the original aws_last_error implementation.
 */
int aws_last_error(void) {
    return tl_last_error;
}
