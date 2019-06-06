/*
 * Copyright 2010-2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/ring_buffer.h>

int aws_ring_buffer_init(struct aws_ring_buffer *ring_buf, struct aws_allocator *allocator, size_t size) {
    AWS_ZERO_STRUCT(*ring_buf);

    ring_buf->allocation = aws_mem_acquire(allocator, size);

    if (!ring_buf->allocation) {
        return AWS_OP_ERR;
    }

    ring_buf->allocator = allocator;
    aws_atomic_store_ptr(&ring_buf->head, ring_buf->allocation);
    aws_atomic_store_ptr(&ring_buf->tail, ring_buf->allocation);
    ring_buf->allocation_end = ring_buf->allocation + size;

    return AWS_OP_SUCCESS;
}

void aws_ring_buffer_clean_up(struct aws_ring_buffer *ring_buf) {
    if (ring_buf->allocation) {
        aws_mem_release(ring_buf->allocator, ring_buf->allocation);
    }

    AWS_ZERO_STRUCT(*ring_buf);
}

int aws_ring_buffer_acquire_hard(struct aws_ring_buffer *ring_buf, size_t requested_size, struct aws_byte_buf *dest) {
    if (requested_size == 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    uint8_t *tail_cpy = aws_atomic_load_ptr(&ring_buf->tail);
    uint8_t *head_cpy = aws_atomic_load_ptr(&ring_buf->head);

    if (tail_cpy > head_cpy) {
        size_t space = tail_cpy - head_cpy - 1;

        if (space >= requested_size) {
            aws_atomic_store_ptr(&ring_buf->head, head_cpy + requested_size);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            return AWS_OP_SUCCESS;
        }

    } else if (tail_cpy <= head_cpy) {
        if ((size_t)(ring_buf->allocation_end - head_cpy) >= requested_size) {
            aws_atomic_store_ptr(&ring_buf->head, head_cpy + requested_size);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            return AWS_OP_SUCCESS;
        }

        if ((size_t)(tail_cpy - ring_buf->allocation) > requested_size) {
            aws_atomic_store_ptr(&ring_buf->head, ring_buf->allocation + requested_size);
            *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, requested_size);
            return AWS_OP_SUCCESS;
        }
    }

    return aws_raise_error(AWS_ERROR_NO_AVAILABLE_BUFFERS);
}

int aws_ring_buffer_acquire_soft(struct aws_ring_buffer *ring_buf, size_t requested_size, struct aws_byte_buf *dest) {
    if (requested_size == 0) {
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    uint8_t *tail_cpy = aws_atomic_load_ptr(&ring_buf->tail);
    uint8_t *head_cpy = aws_atomic_load_ptr(&ring_buf->head);

    if (tail_cpy > head_cpy) {
        size_t space = tail_cpy - head_cpy - 1;

        size_t returnable_size = space > requested_size ? requested_size : space;

        if (space >= returnable_size) {
            aws_atomic_store_ptr(&ring_buf->head, head_cpy + returnable_size);
            *dest = aws_byte_buf_from_empty_array(head_cpy, returnable_size);
            return AWS_OP_SUCCESS;
        }

    } else if (tail_cpy <= head_cpy) {
        size_t head_space = ring_buf->allocation_end - head_cpy;
        size_t tail_space = tail_cpy - ring_buf->allocation;

        if (!head_space && tail_space <= 1) {
            return aws_raise_error(AWS_ERROR_NO_AVAILABLE_BUFFERS);
        }

        if (head_space >= requested_size) {
            aws_atomic_store_ptr(&ring_buf->head, head_cpy + requested_size);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            return AWS_OP_SUCCESS;
        }

        if (tail_space > requested_size) {
            aws_atomic_store_ptr(&ring_buf->head, ring_buf->allocation + requested_size);
            *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, requested_size);
            return AWS_OP_SUCCESS;
        }


        if (head_space > tail_space) {
            aws_atomic_store_ptr(&ring_buf->head, head_cpy + head_space);
            *dest = aws_byte_buf_from_empty_array(head_cpy, head_space);
            return AWS_OP_SUCCESS;
        }

        aws_atomic_store_ptr(&ring_buf->head, ring_buf->allocation + tail_space);
        *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, tail_space);
        return AWS_OP_SUCCESS;
    }

    return aws_raise_error(AWS_ERROR_NO_AVAILABLE_BUFFERS);
}

static inline bool s_buf_belongs_to_pool(const struct aws_ring_buffer *ring_buffer, const struct aws_byte_buf *buf) {
    return buf->buffer >= ring_buffer->allocation && buf->buffer + buf->capacity <= ring_buffer->allocation_end;
}

void aws_ring_buffer_release(struct aws_ring_buffer *ring_buffer, const struct aws_byte_buf *buf) {
    AWS_ASSERT(s_buf_belongs_to_pool(ring_buffer, buf));
    aws_atomic_store_ptr(&ring_buffer->tail, buf->buffer + buf->capacity);
}

bool aws_ring_buffer_buf_belongs_to_pool(const struct aws_ring_buffer *ring_buffer, const struct aws_byte_buf *buf) {
    return s_buf_belongs_to_pool(ring_buffer, buf);
}
