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

#include <aws/common/byte_buf.h>

int aws_ring_buffer_init(struct aws_ring_buffer *ring_buf, struct aws_allocator *allocator, size_t size) {
    AWS_PRECONDITION(ring_buf != NULL);
    AWS_PRECONDITION(allocator != NULL);
    AWS_ZERO_STRUCT(*ring_buf);

    ring_buf->allocation = aws_mem_acquire(allocator, size);

    if (!ring_buf->allocation) {
        return AWS_OP_ERR;
    }

    ring_buf->allocator = allocator;
    aws_atomic_init_ptr(&ring_buf->head, ring_buf->allocation);
    aws_atomic_init_ptr(&ring_buf->tail, ring_buf->allocation);
    ring_buf->allocation_end = ring_buf->allocation + size;

    AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
    return AWS_OP_SUCCESS;
}

void aws_ring_buffer_clean_up(struct aws_ring_buffer *ring_buf) {
    if (ring_buf->allocation) {
        aws_mem_release(ring_buf->allocator, ring_buf->allocation);
    }

    AWS_ZERO_STRUCT(*ring_buf);
}

int aws_ring_buffer_acquire(struct aws_ring_buffer *ring_buf, size_t requested_size, struct aws_byte_buf *dest) {
    AWS_PRECONDITION(aws_ring_buffer_is_valid(ring_buf));
    AWS_PRECONDITION(aws_byte_buf_is_valid(dest));
    if (requested_size == 0) {
        AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    uint8_t *tail_cpy;
    uint8_t *head_cpy;
    AWS_ATOMIC_LOAD_PTR(tail_cpy, ring_buf, &ring_buf->tail);
    AWS_ATOMIC_LOAD_PTR(head_cpy, ring_buf, &ring_buf->head);

    /* this branch is, we don't have any vended buffers. */
    if (head_cpy == tail_cpy) {
        size_t ring_space = ring_buf->allocation_end - ring_buf->allocation;

        if (requested_size > ring_space) {
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return aws_raise_error(AWS_ERROR_OOM);
        }
        AWS_ATOMIC_STORE_PTR(ring_buf->allocation + requested_size, ring_buf, &ring_buf->head);
        AWS_ATOMIC_STORE_PTR(ring_buf->allocation, ring_buf, &ring_buf->tail);
        *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, requested_size);
        AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return AWS_OP_SUCCESS;
    }

    /* you'll constantly bounce between the next two branches as the ring buffer is traversed. */
    /* after N + 1 wraps */
    if (tail_cpy > head_cpy) {
        size_t space = tail_cpy - head_cpy - 1;

        if (space >= requested_size) {
            AWS_ATOMIC_STORE_PTR(head_cpy + requested_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }
        /* After N wraps */
    } else if (tail_cpy < head_cpy) {
        /* prefer the head space for efficiency. */
        if ((size_t)(ring_buf->allocation_end - head_cpy) >= requested_size) {
            AWS_ATOMIC_STORE_PTR(head_cpy + requested_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }

        if ((size_t)(tail_cpy - ring_buf->allocation) > requested_size) {
            AWS_ATOMIC_STORE_PTR(ring_buf->allocation + requested_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, requested_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }
    }

    AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return aws_raise_error(AWS_ERROR_OOM);
}

int aws_ring_buffer_acquire_up_to(
    struct aws_ring_buffer *ring_buf,
    size_t minimum_size,
    size_t requested_size,
    struct aws_byte_buf *dest) {
    AWS_PRECONDITION(requested_size >= minimum_size);
    AWS_PRECONDITION(aws_ring_buffer_is_valid(ring_buf));
    AWS_PRECONDITION(aws_byte_buf_is_valid(dest));

    if (requested_size == 0 || minimum_size == 0 || !ring_buf || !dest) {
        AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
    }

    uint8_t *tail_cpy;
    uint8_t *head_cpy;
    AWS_ATOMIC_LOAD_PTR(tail_cpy, ring_buf, &ring_buf->tail);
    AWS_ATOMIC_LOAD_PTR(head_cpy, ring_buf, &ring_buf->head);

    /* this branch is, we don't have any vended buffers. */
    if (head_cpy == tail_cpy) {
        size_t ring_space = ring_buf->allocation_end - ring_buf->allocation;

        size_t allocation_size = ring_space > requested_size ? requested_size : ring_space;

        if (allocation_size < minimum_size) {
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return aws_raise_error(AWS_ERROR_OOM);
        }

        /* go as big as we can. */
        /* we don't have any vended, so this should be safe. */
        AWS_ATOMIC_STORE_PTR(ring_buf->allocation + allocation_size, ring_buf, &ring_buf->head);
        AWS_ATOMIC_STORE_PTR(ring_buf->allocation, ring_buf, &ring_buf->tail);
        *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, allocation_size);
        AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
        AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
        return AWS_OP_SUCCESS;
    }
    /* you'll constantly bounce between the next two branches as the ring buffer is traversed. */
    /* after N + 1 wraps */
    if (tail_cpy > head_cpy) {
        size_t space = tail_cpy - head_cpy;
        /* this shouldn't be possible. */
        AWS_ASSERT(space);
        space -= 1;

        size_t returnable_size = space > requested_size ? requested_size : space;

        if (returnable_size >= minimum_size) {
            AWS_ATOMIC_STORE_PTR(head_cpy + returnable_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(head_cpy, returnable_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }
        /* after N wraps */
    } else if (tail_cpy < head_cpy) {
        size_t head_space = ring_buf->allocation_end - head_cpy;
        size_t tail_space = tail_cpy - ring_buf->allocation;

        /* if you can vend the whole thing do it. Also prefer head space to tail space. */
        if (head_space >= requested_size) {
            AWS_ATOMIC_STORE_PTR(head_cpy + requested_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(head_cpy, requested_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }

        if (tail_space > requested_size) {
            AWS_ATOMIC_STORE_PTR(ring_buf->allocation + requested_size, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, requested_size);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }

        /* now vend as much as possible, once again preferring head space. */
        if (head_space >= minimum_size && head_space >= tail_space) {
            AWS_ATOMIC_STORE_PTR(head_cpy + head_space, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(head_cpy, head_space);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }

        if (tail_space > minimum_size) {
            AWS_ATOMIC_STORE_PTR(ring_buf->allocation + tail_space - 1, ring_buf, &ring_buf->head);
            *dest = aws_byte_buf_from_empty_array(ring_buf->allocation, tail_space - 1);
            AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
            AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
            return AWS_OP_SUCCESS;
        }
    }

    AWS_POSTCONDITION(aws_ring_buffer_is_valid(ring_buf));
    AWS_POSTCONDITION(aws_byte_buf_is_valid(dest));
    return aws_raise_error(AWS_ERROR_OOM);
}

static inline bool s_buf_belongs_to_pool(const struct aws_ring_buffer *ring_buffer, const struct aws_byte_buf *buf) {
    return buf->buffer >= ring_buffer->allocation && buf->buffer + buf->capacity <= ring_buffer->allocation_end;
}

void aws_ring_buffer_release(struct aws_ring_buffer *ring_buffer, struct aws_byte_buf *buf) {
    AWS_ASSERT(s_buf_belongs_to_pool(ring_buffer, buf));
    aws_atomic_store_ptr(&ring_buffer->tail, buf->buffer + buf->capacity);
    AWS_ZERO_STRUCT(*buf);
}

bool aws_ring_buffer_buf_belongs_to_pool(const struct aws_ring_buffer *ring_buffer, const struct aws_byte_buf *buf) {
    return s_buf_belongs_to_pool(ring_buffer, buf);
}
