/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/byte_handle.h>

static void s_byte_handle_destroy(void *user_data) {
    struct aws_byte_handle *byte_handle = user_data;
    if (byte_handle->destroy) {
        byte_handle->destroy(byte_handle);
    }
}

void aws_byte_handle_init_base(
    struct aws_byte_handle *byte_handle,
    struct aws_allocator *alloc,
    struct aws_byte_cursor data,
    aws_byte_handle_destroy_fn *destroy,
    void *impl) {

    AWS_PRECONDITION(aws_byte_cursor_is_valid(&data));

    byte_handle->alloc = alloc;
    byte_handle->data = data;
    byte_handle->destroy = destroy;
    byte_handle->impl = impl;
    aws_ref_count_init(&byte_handle->ref_count, byte_handle, s_byte_handle_destroy);
}

struct aws_byte_handle *aws_byte_handle_acquire(const struct aws_byte_handle *byte_handle) {
    AWS_PRECONDITION(byte_handle);
    return aws_ref_count_acquire(&((struct aws_byte_handle *)byte_handle)->ref_count);
}

struct aws_byte_handle *aws_byte_handle_release(const struct aws_byte_handle *byte_handle) {
    if (byte_handle != NULL) {
        aws_ref_count_release(&((struct aws_byte_handle *)byte_handle)->ref_count);
    }
    return NULL;
}

struct aws_byte_cursor aws_byte_handle_data(const struct aws_byte_handle *byte_handle) {
    return byte_handle->data;
}

/*******************************************************************************
 * SLICE
 ******************************************************************************/

struct aws_byte_handle_slice {
    struct aws_byte_handle base;
    const struct aws_byte_handle *source;
};

static void s_byte_handle_slice_destroy(struct aws_byte_handle *byte_handle) {
    struct aws_byte_handle_slice *handle_impl = byte_handle->impl;
    aws_byte_handle_release(handle_impl->source);
    aws_mem_release(handle_impl->base.alloc, handle_impl);
}

struct aws_byte_handle *aws_byte_handle_new_slice(
    struct aws_allocator *alloc,
    struct aws_byte_cursor slice,
    const struct aws_byte_handle *source) {

    AWS_PRECONDITION(source != NULL);
    AWS_PRECONDITION(aws_byte_cursor_is_valid(&slice));
    AWS_PRECONDITION(
        (slice.ptr >= aws_byte_handle_data(source).ptr) &&
        (slice.ptr + slice.len <= aws_byte_handle_data(source).ptr + aws_byte_handle_data(source).len));

    struct aws_byte_handle_slice *handle_impl = aws_mem_calloc(alloc, 1, sizeof(struct aws_byte_handle_slice));
    aws_byte_handle_init_base(&handle_impl->base, alloc, slice, s_byte_handle_slice_destroy, handle_impl);

    handle_impl->source = aws_byte_handle_acquire(source);

    return &handle_impl->base;
}

/*******************************************************************************
 * OWNING BYTE_BUF
 ******************************************************************************/

struct aws_byte_handle_owning_byte_buf {
    struct aws_byte_handle base;
    struct aws_byte_buf source;
};

static void s_byte_handle_owning_byte_buf_destroy(struct aws_byte_handle *byte_handle) {
    struct aws_byte_handle_owning_byte_buf *handle_impl = byte_handle->impl;

    aws_byte_buf_clean_up(&handle_impl->source);
    aws_mem_release(handle_impl->base.alloc, handle_impl);
}

struct aws_byte_handle *aws_byte_handle_new_take_byte_buf(
    struct aws_allocator *alloc,
    struct aws_byte_buf *source_buf) {

    AWS_PRECONDITION(aws_byte_buf_is_valid(source_buf));

    struct aws_byte_handle_owning_byte_buf *handle_impl =
        aws_mem_calloc(alloc, 1, sizeof(struct aws_byte_handle_owning_byte_buf));

    aws_byte_handle_init_base(
        &handle_impl->base,
        alloc,
        aws_byte_cursor_from_buf(source_buf),
        s_byte_handle_owning_byte_buf_destroy,
        handle_impl);

    /* Take ownership of aws_byte_buf's contents.
     * Zero out the old aws_byte_buf to avoid double-free */
    handle_impl->source = *source_buf;
    AWS_ZERO_STRUCT(*source_buf);

    return &handle_impl->base;
}
