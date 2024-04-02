#ifndef AWS_COMMON_CBOR_H
#define AWS_COMMON_CBOR_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/common.h>

AWS_PUSH_SANE_WARNING_LEVEL
AWS_EXTERN_C_BEGIN

struct aws_cbor_item;

struct aws_cbor_encoder {
    struct aws_allocator *alloca;
    struct aws_byte_buf buffer;
};

AWS_COMMON_API
int aws_cbor_encode_uint_append(struct aws_byte_buf *to, uint64_t value);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif // AWS_COMMON_CBOR_H
