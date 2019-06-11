#ifndef AWS_COMMON_RING_BUFFER_H
#define AWS_COMMON_RING_BUFFER_H
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

#include <aws/common/atomics.h>

#ifdef CBMC
#    define AWS_ATOMIC_LOAD_PTR(dest_ptr, ring_buf, atomic_ptr)                                                        \
        dest_ptr = aws_atomic_load_ptr(atomic_ptr);                                                                    \
        assert(__CPROVER_POINTER_OBJECT(dest_ptr) == __CPROVER_POINTER_OBJECT(ring_buf->allocation));                  \
        assert(aws_ring_buffer_check_atomic_ptr(ring_buf, dest_ptr));
#    define AWS_ATOMIC_STORE_PTR(src_ptr, ring_buf, atomic_ptr)                                                        \
        assert(aws_ring_buffer_check_atomic_ptr(ring_buf, src_ptr));                                                   \
        aws_atomic_store_ptr(atomic_ptr, src_ptr);
#else
#    define AWS_ATOMIC_LOAD_PTR(dest_ptr, ring_buf, atomic_ptr) dest_ptr = aws_atomic_load_ptr(atomic_ptr);
#    define AWS_ATOMIC_STORE_PTR(src_ptr, ring_buf, atomic_ptr) aws_atomic_store_ptr(atomic_ptr, src_ptr);
#endif

/**
 * Lockless ring buffer implementation that is thread safe assuming a single thread acquires and a single thread
 * releases. For any other use case (other than the single-threaded use-case), you must manage thread-safety manually.
 *
 * Also, a very important note: release must happen in the same order as acquire. If you do not your application, and
 * possibly computers within a thousand mile radius, may die terrible deaths, and the local drinking water will be
 * poisoned for generations with fragments of what is left of your radioactive corrupted memory.
 */
struct aws_ring_buffer {
    struct aws_allocator *allocator;
    uint8_t *allocation;
    struct aws_atomic_var head;
    struct aws_atomic_var tail;
    uint8_t *allocation_end;
};

struct aws_byte_buf;

AWS_EXTERN_C_BEGIN

/**
 * Initializes a ring buffer with an allocation of size `size`. Returns AWS_OP_SUCCESS on a successful initialization,
 * AWS_OP_ERR otherwise.
 */
AWS_COMMON_API int aws_ring_buffer_init(struct aws_ring_buffer *ring_buf, struct aws_allocator *allocator, size_t size);

/**
 * Evaluates the set of properties that define the shape of all valid aws_ring_buffer structures.
 * It is also a cheap check, in the sense it run in constant time (i.e., no loops or recursion).
 */
AWS_STATIC_IMPL bool aws_ring_buffer_is_valid(const struct aws_ring_buffer *const ring_buf) {
    return ring_buf && AWS_MEM_IS_READABLE(ring_buf->allocation, ring_buf->allocation_end - ring_buf->allocation) &&
           (ring_buf->allocator != NULL);
}

/*
 * Checks whether atomic_ptr correctly points to a memory location within the bounds of the aws_ring_buffer
 */
AWS_STATIC_IMPL bool aws_ring_buffer_check_atomic_ptr(struct aws_ring_buffer *const ring_buf, uint8_t *atomic_ptr) {
    return (atomic_ptr >= ring_buf->allocation && atomic_ptr <= ring_buf->allocation_end);
}

/**
 * Cleans up the ring buffer's resources.
 */
AWS_COMMON_API void aws_ring_buffer_clean_up(struct aws_ring_buffer *ring_buf);

/**
 * Attempts to acquire `requested_size` buffer and stores the result in `dest` if successful. Returns AWS_OP_SUCCESS if
 * the requested size was available for use, AWS_OP_ERR otherwise.
 */
AWS_COMMON_API int aws_ring_buffer_acquire(
    struct aws_ring_buffer *ring_buf,
    size_t requested_size,
    struct aws_byte_buf *dest);

/**
 * Attempts to acquire `requested_size` buffer and stores the result in `dest` if successful. If not available, it will
 * attempt to acquire anywhere from 1 byte to `requested_size`. Returns AWS_OP_SUCCESS if some buffer space is available
 * for use, AWS_OP_ERR otherwise.
 */
AWS_COMMON_API int aws_ring_buffer_acquire_up_to(
    struct aws_ring_buffer *ring_buf,
    size_t minimum_size,
    size_t requested_size,
    struct aws_byte_buf *dest);

/**
 * Releases `buf` back to the ring buffer for further use. RELEASE MUST HAPPEN in the SAME ORDER AS ACQUIRE.
 * If you do not, your application, and possibly computers within a thousand mile radius, may die terrible deaths,
 * and the local drinking water will be poisoned for generations
 * with fragments of what is left of your radioactive corrupted memory.
 */
AWS_COMMON_API void aws_ring_buffer_release(struct aws_ring_buffer *ring_buffer, struct aws_byte_buf *buf);

/**
 * Returns true if the memory in `buf` was vended by this ring buffer, false otherwise.
 * Make sure `buf->buffer` and `ring_buffer->allocation` refer to the same memory region.
 */
AWS_COMMON_API bool aws_ring_buffer_buf_belongs_to_pool(
    const struct aws_ring_buffer *ring_buffer,
    const struct aws_byte_buf *buf);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_RING_BUFFER_H */
