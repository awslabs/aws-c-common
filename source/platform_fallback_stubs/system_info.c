/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/private/system_info_priv.h>

#include <aws/common/logging.h>

int aws_system_environment_load_platform_impl(struct aws_system_environment *env) {
    (void)env;
    AWS_LOGF_DEBUG(
        AWS_LS_COMMON_GENERAL,
        "id=%p: platform specific environment loading is not implemented for this platform.",
        (void *)env);

    return AWS_OP_SUCCESS;
}

void aws_system_environment_destroy_platform_impl(struct aws_system_environment *env) {
    (void)env;
}
