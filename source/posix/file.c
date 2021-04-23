/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/file.h>
#include <stdio.h>

FILE *aws_fopen(const char *file_path, const char *mode) {
    return fopen(file_path, mode);
}
