#ifndef AWS_COMMON_FUTURE_H
#define AWS_COMMON_FUTURE_H

/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

AWS_EXTERN_C_BEGIN

/**
 * A future represents an operation that may need to complete asynchronously.
 * The future will be "complete" when it holds a result value or error code.
 *
 * The "producer" is responsible for completing the future,
 * setting the result value or error code.
 *
 * The "consumer" waits until the future is complete,
 * before taking ownership of the result value.
 *
 * There are several ways for the consumer to determine a future is complete:
 *
 * 1) aws_future_is_complete()
 *      Query whether the future is already complete.
 *
 * 2) aws_future_set_completion_callback()
 *      Set a callback that fires once when the future completes.
 *      WARNING: The callback may fire synchronously, if that scares you see the next method...
 *
 * 3) aws_future_is_complete_else_set_callback()
 *      A combo of the previous 2 methods. The completion callback is only
 *      set if it is guaranteed to fire asynchronously (on another thread,
 *      or on this thread but later after this function returns).
 *
 * 4) aws_future_wait_until_complete():
 *      Block the current thread until the future completes.
 *      Risks deadlock if used on event threads,
 *      but useful for unit tests and samples.
 */
struct aws_future;

/**
 * Invoked exactly once when the future is complete.
 * You can now call aws_future_take_result() and aws_future_get_error() with confidence.
 */
typedef void(aws_future_on_complete_fn)(void *user_data);

typedef void(aws_future_value_dtor_fn)(void *value);

/**
 * Create a new, incomplete, future with a reference count of 1.
 * This function cannot fail.
 */
AWS_COMMON_API
struct aws_future *aws_future_new(struct aws_allocator *alloc);

/**
 * Release the future for cleanup by decrementing its reference count.
 * This is the only function you MAY pass NULL to.
 * NULL is ALWAYS returned from this function.
 * After calling this, you MUST NOT touch the future again.
 *
 * If you are the producer, you MUST set the result (or error), before calling this.
 * If you are the consumer, you MUST take ownership of the result before calling this.
 */
AWS_COMMON_API
struct aws_future *aws_future_release(struct aws_future *future);

/**
 * Acquire a hold on the future by incrementing its reference count.
 * Returns the same pointer that is passed in.
 */
AWS_COMMON_API
struct aws_future *aws_future_acquire(struct aws_future *future);

/**
 * Set the future as complete, with a successful result value.
 * Only the producer should call this.
 * The value MUST be non-NULL.
 * This MUST NOT be called if the future is already complete.
 * The dtor is optional, it is only called if the consumer never takes ownership of the value.
 */
AWS_COMMON_API
void aws_future_set_value(struct aws_future *future, void *value, aws_future_value_dtor_fn *dtor);

/**
 * Set the future as complete, with an error.
 * Only the producer should call this.
 *
 * If AWS_OP_SUCCESS is returned, then the future is now complete with the
 * given error_code.
 *
 * This function can only fail if the future is already complete.
 * In this case, AWS_OP_ERR is returned and AWS_ERROR_FUTURE_ALREADY_COMPLETE is raised.
 * You probably don't care whether AWS_OP_SUCCESS or AWS_OP_ERR is returned,
 * since the future is complete either way.
 * TODO: just remove error code?
 */
AWS_COMMON_API
int aws_future_set_error(struct aws_future *future, int error_code);

/**
 * Return true if the future is complete.
 * If true, now is the time to call aws_future_get_result()
 * and if that returns NULL call aws_future_get_error();
 *
 * If you want to be informed when the future is complete, use one of:
 * - aws_future_set_completion_callback()
 * - aws_future_is_complete_else_set_callback()
 */
AWS_COMMON_API
bool aws_future_is_complete(const struct aws_future *future);

/**
 * Set a callback to be invoked when the future is complete.
 * The callback is guaranteed to fire exactly once.
 *
 * The callback can fire at ANY time.
 * If the future completes on another thread, it will fire from that thread,
 * which could theoretically happen before this function returns.
 *
 * If the future is already complete, the callback will fire synchronously on this
 * thread before this function can return. If you do not want the callback
 * to fire synchronously on this thread, use aws_future_is_complete_else_set_callback().
 *
 * If successful, AWS_OP_SUCCESS is returned.
 * This can only fail if a completion callback has already been set,
 * in which case AWS_OP_ERR is returned and AWS_ERROR_FUTURE_CALLBACK_ALREADY_SET is raised.
 * TODO: this can be void function if we fatally assert it's used correctly, or store an array of callbacks?
 */
AWS_COMMON_API
void aws_future_set_completion_callback(
    struct aws_future *future,
    aws_future_on_complete_fn *on_complete,
    void *user_data);

/**
 * Learn that the future is already complete, or register a callback
 * that will be invoked when the future is completed asynchronously.
 *
 * If the future is already complete, true is returned and the callback
 * will never be invoked.
 *
 * If the future is incomplete, false is returned.
 * The callback will be invoked (always asynchronously) when the future finally completes.
 *
 * You MUST NOT call this if a callback is already registered.
 */
AWS_COMMON_API
bool aws_future_is_complete_else_set_callback(
    struct aws_future *future,
    aws_future_on_complete_fn *on_complete,
    void *on_complete_user_data);

/**
 * Block this thread until the future is complete.
 * You probably only want to do this in unit tests, on the main thread.
 * There is a huge risk of deadlocking the program if this is called from an event-loop thread.
 *
 * Returns true if the future completes within the timeout duration.
 */
AWS_COMMON_API
bool aws_future_wait_until_complete(struct aws_future, uint64_t timeout_ns);

/**
 * Take the result value of a completed future.
 * Only the consumer should call this.
 *
 * If the future completed successfully, the value is returned.
 * You own the value now, the future will not try to clean it up.
 *
 * If the future completed with an error, NULL is returned.
 * Call aws_last_error() to get the error_code.
 *
 * You MUST NOT call this on an incomplete future.
 * You MUST NOT call this multiple times.
 */
void *aws_future_take_value(struct aws_future *future);

/* TODO:
    -   simple API vs minimizing locks
    -   do like C++ and separate producer/consumer APIs into promise/future?
    -   should future release result?
        -   if so, set_result_with_cleanup() could be a void function
        -   forces refcounting?
    -   on_complete passes result and error_code to reduce locking?
    -   support for cancel? If so, does that complete future automatically, or is it up to the producer?
        downside of automatic completion is that set_result() calls are always at risk of failing */

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FUTURE_H */
