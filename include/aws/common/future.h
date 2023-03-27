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
 * setting the result or error code.
 *
 * The "consumer" is responsible for waiting until the future is complete,
 * and taking ownership of the result (the future doesn't know how to clean
 * up the result).
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
 * You can now call aws_future_get_result() and aws_future_get_error() with confidence.
 */
void aws_future_complete_fn(void *user_data);

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
 * After calling this, you MUST not touch the future again.
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
 * Set the future as complete, with a successful result.
 * Only the producer should call this.
 *
 * TODO: warn about callbacks firing
 * TODO: maybe just one function that combines set_result/set_error?
 *
 * If AWS_OP_SUCCESS is returned, then future is now complete with the given result.
 * The result is stored by pointer within the future and the consumer.
 * Note the the future will not clean up the result,
 * it is up to the consumer to call aws_future_get_result() and take ownership.
 *
 * This function can only fail if the future is already complete.
 * In this case, AWS_OP_ERR is returned and AWS_ERROR_FUTURE_ALREADY_COMPLETE is raised,
 * and the future does NOT take ownership of the result so you must clean it up.
 */
AWS_COMMON_API
int aws_future_set_result(struct aws_future *future, void *result);

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
int aws_future_set_completion_callback(struct aws_future *future, aws_future_complete_fn *on_complete, void *user_data);

/**
 * Determine that the future is complete,
 * or register a callback to learn asynchronously when the future is complete.
 *
 * If the future is already complete AWS_OP_SUCCESS is returned, out_is_complete is set true,
 * and the on_complete callback will never be invoked.
 *
 * If the future is incomplete, AWS_OP_SUCCESS is returned, out_is_complete is set false,
 * and the on_complete callback will be invoked exactly once.
 * The callback will never be invoked synchronously (on this thread before this function call returns).
 *
 * This function can only fail if a completion callback has already been set,
 * in which case AWS_OP_ERR is returned and AWS_ERROR_FUTURE_CALLBACK_ALREADY_SET is raised.
 * TODO: this could return a bool if we fatally assert it's used correctly, or store an array of callbacks?
 */
AWS_COMMON_API
int aws_future_is_complete_else_set_callback(
    struct aws_future *future,
    aws_completion_fn *on_complete,
    void *user_data,
    bool *out_is_complete);

/**
 * Block this thread until the future is complete.
 * You probably only want to do this in unit tests, on the main thread.
 * There is a huge risk of deadlocking the program if this is called from an event-loop thread.
 *
 * If the future completes within the timeout duration, then AWS_OP_SUCCESS is returned.
 *
 * Otherwise, AWS_OP_ERR is returned.
 * If the future did not complete within the wait duration, then AWS_ERROR_FUTURE_WAIT_TIMEOUT is raised.
 * If a callback is already set then AWS_ERROR_FUTURE_CALLBACK_ALREADY_SET is raised.
 * There are no other possible errors.
 */
AWS_COMMON_API
int aws_future_wait_until_complete(struct aws_future, uint64_t timeout_ns); /*TODO: milliseconds? */

/**
 * Get the result of a completed future.
 * Only the consumer should call this.
 *
 * If the future completed successfully, the result is returned by pointer.
 * You own the result and are responsible for cleaning it up.
 *
 * Otherwise NULL is returned.
 * If the future completed with an error, that error-code is raised.
 * If the future is incomplete, AWS_ERROR_FUTURE_INCOMPLETE is raised.
 */
void *aws_future_get_result(const struct aws_future *future);

/**
 * Get the error code of a completed future.
 * Only the consumer should call this.
 *
 * If the future completed successfully, 0 is returned.
 * If the future completed with an error, that error code is returned.
 * If the future is incomplete, AWS_ERROR_FUTURE_INCOMPLETE is returned.
 */
int aws_future_get_error(const struct aws_future *future);

/* TODO:
    -   do like C++ and separate producer/consumer APIs into promise/future?
    -   support for cancel? If so, does that complete future automatically, or is it up to the producer?
        downside of automatic completion is that set_result() calls are always at risk of failing */

AWS_EXTERN_C_END

#endif /* AWS_COMMON_FUTURE_H */
