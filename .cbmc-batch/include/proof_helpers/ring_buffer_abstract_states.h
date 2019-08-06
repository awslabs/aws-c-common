/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
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
