#ifndef AWS_ASYNC_STREAM_H
#define AWS_ASYNC_STREAM_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/ref_count.h>

AWS_PUSH_SANE_WARNING_LEVEL

struct aws_byte_buf;

struct aws_async_stream {
    const struct aws_async_stream_vtable *vtable;
    struct aws_allocator *alloc;
    struct aws_ref_count ref_count;
    void *impl;
};

typedef void(aws_async_stream_waker_fn)(void *user_data);

struct aws_async_stream_vtable {
    struct aws_async_stream_poll_result (
        *poll)(struct aws_async_stream *stream, aws_async_stream_waker_fn *waker, void *user_data);

    struct aws_future *(*read_once)(struct aws_async_stream *stream, struct aws_byte_buf *dest);

    void (*destroy)(struct aws_async_stream *stream);
};

struct aws_async_stream_poll_result {
    enum aws_async_stream_poll_result_type {
        AWS_ASYNC_STREAM_DATA,
        AWS_ASYNC_STREAM_DONE,
        AWS_ASYNC_STREAM_ERROR,
        AWS_ASYNC_STREAM_PENDING,
    } type;

    union {
        int error_code;
        struct aws_byte_handle *data;
    } u;
};

AWS_EXTERN_C_BEGIN

AWS_COMMON_API
void aws_async_stream_init_base(
    struct aws_async_stream *stream,
    struct aws_allocator *alloc,
    const struct aws_async_stream_vtable *vtable,
    void *impl);

AWS_COMMON_API
struct aws_async_stream *aws_async_stream_acquire(struct aws_async_stream *stream);

AWS_COMMON_API
struct aws_async_stream *aws_async_stream_acquire(struct aws_async_stream *stream);

AWS_COMMON_API
struct aws_async_stream *aws_async_stream_release(struct aws_async_stream *stream);

/**
 * TODO: size_t len_hint?
 * rust: futures::io::AsyncRead.poll_read(self, ctx, out_buf) -> Poll<Result<size_t,Error>
 * java: java.util.concurrent.Flow.Subscription.request(long n) n is num items, not size, so cannot specify max or hint
 * python: async asyncio.StreamReader.read(n=-1) -> bytes: n is max, if -1 then read to end
 */
AWS_COMMON_API
struct aws_async_stream_poll_result aws_async_stream_poll(
    struct aws_async_stream *stream,
    aws_async_stream_waker_fn *waker,
    void *user_data);

/**
 * Read once from the async stream.
 * The read may complete before EOF, and before the buffer is full.
 * Returns an aws_future which will eventually hold a bool indicating EOF, or an error code.
 */
AWS_COMMON_API
struct aws_future *aws_async_stream_read_once(struct aws_async_stream *stream, struct aws_byte_buf *dest);

/**
 * Read from the async stream until the buffer is full or EOF is reached.
 * This may perform multiple read_once() calls under the hood.
 * Returns an aws_future which will eventually hold a bool indicating EOF, or an error code.
 */
AWS_COMMON_API
struct aws_future *aws_async_stream_read_to_fill(struct aws_async_stream *stream, struct aws_byte_buf *dest);

AWS_EXTERN_C_END
AWS_POP_SANE_WARNING_LEVEL

#endif /*AWS_ASYNC_STREAM_H */
