#ifndef AWS_COMMON_REFCOUNT_H
#define AWS_COMMON_REFCOUNT_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/common.h>

#include <aws/common/atomics.h>

typedef void(aws_simple_completion_callback)(void *);

/*
 * A utility type for making ref-counted types, reminiscent of std::shared_ptr in C++
 */
struct aws_ref_count {
    struct aws_atomic_var ref_count;
    void *object;
    aws_simple_completion_callback *on_zero_fn;
};

struct aws_shutdown_callback_options {
    aws_simple_completion_callback *shutdown_callback_fn;
    void *shutdown_callback_user_data;
};

AWS_EXTERN_C_BEGIN

/**
 * Initializes a ref-counter structure.
 *
 * @param ref_count ref-counter to initialize
 * @param object object being ref counted
 * @param on_zero_fn function to invoke when the ref count reaches zero
 */
AWS_COMMON_API void aws_ref_count_init(
    struct aws_ref_count *ref_count,
    void *object,
    aws_simple_completion_callback *on_zero_fn);

/**
 * Increments a ref-counter's ref count
 *
 * @param ref_count ref-counter to increment the count for
 * @return the object being ref-counted
 */
AWS_COMMON_API void *aws_ref_count_acquire(struct aws_ref_count *ref_count);

/**
 * Decrements a ref-counter's ref count.  Invokes the on_zero callback if the ref count drops to zero
 * @param ref_count ref-counter to decrement the count for
 * @return the value of the decremented ref count
 */
AWS_COMMON_API size_t aws_ref_count_release(struct aws_ref_count *ref_count);

/**
 * Utility function that returns when all auxiliary threads created by crt types (event loop groups and
 * host resolvers) have completed and those types have completely cleaned themselves up.  The actual cleanup
 * process may be invoked as a part of a spawned thread, but the wait will not get signalled until that cleanup
 * thread is in its at_exit callback processing loop with no outstanding memory allocations.
 *
 * Primarily used by tests to guarantee that everything is cleaned up before performing a memory check.
 *
 * The synchronization primitives involved are all initialized and cleaned up in library init/cleanup.
 */
AWS_COMMON_API void aws_global_thread_shutdown_wait(void);

/**
 * Increments the global thread tracking count.  Currently invoked on event loop group and host resolver creation.
 *
 * Tracks the number of outstanding thread-generating objects (not the total number of threads generated).
 * Currently this is the number of aws_host_resolver and aws_event_loop_group objects that have not yet been
 * fully cleaned up.
 */
AWS_COMMON_API void aws_global_thread_tracker_increment(void);

/**
 * Decrements the global thread tracking count.  Currently invoked on event loop group and host resolver destruction.
 *
 * Tracks the number of outstanding thread-generating objects (not the total number of threads generated).
 * Currently this is the number of aws_host_resolver and aws_event_loop_group objects that have not yet been
 * fully cleaned up.
 */
AWS_COMMON_API void aws_global_thread_tracker_decrement(void);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_REFCOUNT_H */
