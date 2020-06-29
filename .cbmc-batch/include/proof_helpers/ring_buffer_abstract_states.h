/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#pragma once

/**
 * Ring buffer is empty
 */
bool is_empty_state(struct aws_ring_buffer *ring_buf) {
    uint8_t *head = aws_atomic_load_ptr(&ring_buf->head);
    uint8_t *tail = aws_atomic_load_ptr(&ring_buf->tail);
    return tail == head;
}

/**
 * Ring buffer is valid [allocation==tail...head)
 */
bool is_front_valid_state(struct aws_ring_buffer *ring_buf) {
    uint8_t *head = aws_atomic_load_ptr(&ring_buf->head);
    uint8_t *tail = aws_atomic_load_ptr(&ring_buf->tail);
    return ring_buf->allocation == tail && tail < head;
}

/**
 * Ring buffer is valid [allocation<tail...head) (not front_valid)
 */
bool is_middle_valid_state(struct aws_ring_buffer *ring_buf) {
    uint8_t *head = aws_atomic_load_ptr(&ring_buf->head);
    uint8_t *tail = aws_atomic_load_ptr(&ring_buf->tail);
    return ring_buf->allocation < tail && tail < head;
}

/**
 * Ring buffer is valid [allocation...head) and [tail...allocation_end)
 */
bool is_ends_valid_state(struct aws_ring_buffer *ring_buf) {
    uint8_t *head = aws_atomic_load_ptr(&ring_buf->head);
    uint8_t *tail = aws_atomic_load_ptr(&ring_buf->tail);
    return tail > head;
}
