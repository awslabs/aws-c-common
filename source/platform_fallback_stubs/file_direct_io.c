/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/environment.h>
#include <aws/common/file.h>
#include <aws/common/logging.h>
#include <aws/common/string.h>

int aws_file_path_read_from_offset_direct_io(
    const struct aws_string *file_path,
    uint64_t offset,
    size_t max_read_length,
    struct aws_byte_buf *output_buf,
    size_t *out_actual_read) {
    (void)file_path;
    (void)offset;
    (void)max_read_length;
    (void)output_buf;
    (void)out_actual_read;
    /* TODO: Support it cross different platforms. */
    AWS_LOGF_ERROR(AWS_LS_COMMON_GENERAL, "Direct file IO is not supported yet on platforms other than linux.");
    return aws_raise_error(AWS_ERROR_UNSUPPORTED_OPERATION);
}
