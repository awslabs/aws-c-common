#ifndef AWS_BYTE_HANDLE_H
#define AWS_BYTE_HANDLE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_buf.h>
#include <aws/common/ref_count.h>

struct aws_byte_handle;

typedef void(aws_byte_handle_destroy_fn)(struct aws_byte_handle *);

struct aws_byte_handle {
    struct aws_allocator *alloc;
    struct aws_ref_count ref_count;
    struct aws_byte_cursor data;
    aws_byte_handle_destroy_fn *destroy;
    void *impl;
};

/* TODO
-   what about languages that can't pin their memory? will this really work in java/swift
    would we need to move to a read_into model?

    size_t aws_byte_handle_size();
    int aws_byte_handle_read_into(struct aws_byte_handle *byte_handle, void *dst, size_t offset, size_t len);

    benefit of this is that a single byte_handle could also wrap a set of byte_handles
*/

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_byte_handle_init_base(
    struct aws_byte_handle *byte_handle,
    struct aws_allocator *alloc,
    struct aws_byte_cursor data,
    aws_byte_handle_destroy_fn *destroy,
    void *impl);

/**
 * Create a new aws_byte_handle, referring to a subset of bytes from another aws_byte_handle.
 */
AWS_COMMON_API
struct aws_byte_handle *aws_byte_handle_new_slice(
    struct aws_allocator *alloc,
    struct aws_byte_cursor slice,
    const struct aws_byte_handle *source);

/**
 * Create a new aws_byte_handle which takes ownership of an aws_byte_buf.
 */
AWS_COMMON_API
struct aws_byte_handle *aws_byte_handle_new_take_byte_buf(struct aws_allocator *alloc, struct aws_byte_buf *source_buf);

AWS_COMMON_API
struct aws_byte_handle *aws_byte_handle_acquire(const struct aws_byte_handle *byte_handle);

AWS_COMMON_API
struct aws_byte_handle *aws_byte_handle_release(const struct aws_byte_handle *byte_handle);

AWS_COMMON_API
struct aws_byte_cursor aws_byte_handle_data(const struct aws_byte_handle *byte_handle);

AWS_EXTERN_C_END

#endif /*AWS_BYTE_HANDLE_H */
