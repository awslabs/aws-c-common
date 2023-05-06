/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/async_stream.h>

#include <aws/common/byte_buf.h>
#include <aws/common/future.h>

void aws_async_stream_init_base(
    struct aws_async_stream *stream,
    struct aws_allocator *alloc,
    const struct aws_async_stream_vtable *vtable,
    void *impl) {

    AWS_ZERO_STRUCT(*stream);
    stream->alloc = alloc;
    stream->vtable = vtable;
    stream->impl = impl;
    aws_ref_count_init(&stream->ref_count, stream, (aws_simple_completion_callback *)vtable->destroy);
}

struct aws_async_stream *aws_async_stream_acquire(struct aws_async_stream *stream) {
    if (stream != NULL) {
        aws_ref_count_acquire(&stream->ref_count);
    }
    return stream;
}

struct aws_async_stream *aws_async_stream_release(struct aws_async_stream *stream) {
    if (stream) {
        aws_ref_count_release(&stream->ref_count);
    }
    return NULL;
}

struct aws_future *aws_async_stream_read_once(struct aws_async_stream *stream, struct aws_byte_buf *dest) {
    /* Deal with this edge case here, instead of relying on every implementation to do it right. */
    if (dest->len == dest->capacity) {
        struct aws_future *future = aws_future_new(stream->alloc, AWS_FUTURE_BOOL);
        aws_future_set_error(future, AWS_ERROR_SHORT_BUFFER);
        return future;
    }

    return stream->vtable->read_once(stream, dest);
}

/* Data to perform the aws_async_stream_read_to_fill() operation */
struct aws_async_stream_fill_operation {
    struct aws_async_stream *stream;
    struct aws_byte_buf *dest;
    struct aws_future *future;
};

static void s_async_stream_fill_operation_complete(
    struct aws_async_stream_fill_operation *operation,
    bool eof,
    int error_code) {

    if (error_code) {
        aws_future_set_error(operation->future, error_code);
    } else {
        aws_future_set_bool(operation->future, eof);
    }
    aws_future_release(operation->future);

    struct aws_async_stream *stream = operation->stream;
    aws_mem_release(stream->alloc, operation);
    aws_async_stream_release(stream);
}

/* Call read_once() in a loop.
 * It would be simpler to set a completion callback for each read_once() call,
 * but this risks our call stack growing large if there are many small, synchronous, reads.
 * So be complicated and loop until a read_once call is actually async,
 * and only then set the completion callback (which is this same function, where we resume looping). */
static void s_async_stream_fill_operation_loop(struct aws_future *read1_future, void *user_data) {
    struct aws_async_stream_fill_operation *operation = user_data;

    while (true) {
        /* Process read1_future from previous iteration of loop.
         * It's NULL the first time the operation ever enters the loop.
         * But it's set in subsequent runs of the loop, and when this is a read1_future completion callback. */
        if (read1_future) {
            if (aws_future_is_done_else_register_callback(
                    read1_future, s_async_stream_fill_operation_loop, operation)) {
                /* read1_future is done */
                int error_code = aws_future_get_error(read1_future);
                bool eof = error_code ? false : aws_future_get_bool(read1_future);
                bool reached_capacity = operation->dest->len == operation->dest->capacity;
                read1_future = aws_future_release(read1_future);

                if (error_code || eof || reached_capacity) {
                    /* operation complete! */
                    s_async_stream_fill_operation_complete(operation, eof, error_code);
                    return;
                }
            } else {
                /* callback registered, we'll resume this loop later */
                return;
            }
        }

        /* Kick off a read, which may or may not complete async */
        read1_future = aws_async_stream_read_once(operation->stream, operation->dest);
    }
}

struct aws_future *aws_async_stream_read_to_fill(struct aws_async_stream *stream, struct aws_byte_buf *dest) {

    struct aws_future *future = aws_future_new(stream->alloc, AWS_FUTURE_BOOL);

    /* Deal with this edge case here, instead of relying on every implementation to do it right. */
    if (dest->len == dest->capacity) {
        aws_future_set_error(future, AWS_ERROR_SHORT_BUFFER);
        return future;
    }

    struct aws_async_stream_fill_operation *operation =
        aws_mem_calloc(stream->alloc, 1, sizeof(struct aws_async_stream_fill_operation));
    operation->stream = aws_async_stream_acquire(stream);
    operation->dest = dest;
    operation->future = aws_future_acquire(future);

    /* Kick off work  */
    s_async_stream_fill_operation_loop(NULL, operation);

    /* TODO: OOHHHH DANG if future completes synchronously then its refcount goes to 0
     * maybe have 2 separate objects to make refcount accidents harder? */
    return future;
}

struct aws_async_stream_poll_result aws_async_stream_poll(
    struct aws_async_stream *stream,
    aws_async_stream_waker_fn *waker,
    void *user_data) {

    return stream->vtable->poll(stream, waker, user_data);
}
