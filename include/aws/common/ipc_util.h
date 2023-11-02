#ifndef AWS_COMMON_IPC_UTIL_H
#define AWS_COMMON_IPC_UTIL_H
/**
* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
* SPDX-License-Identifier: Apache-2.0.
*/
#include <aws/common/common.h>
#include <aws/common/byte_buf.h>

struct aws_ipc_util_instance_lock;
AWS_EXTERN_C_BEGIN

/**
 * Attempts to acquire a system-wide (not per process or per user) lock scoped by instance_nonce.
 * For any given unique nonce, a lock will be returned by the first caller. Subsequent calls will
 * return NULL until the either the process owning the lock exits or the program owning the lock
 * calls aws_ipc_util_instance_lock_release() explicitly.
 *
 * If the process exits before the lock is released, the kernel will unlock it for the next consumer.
 */
AWS_COMMON_API
struct aws_ipc_util_instance_lock *aws_ipc_util_instance_lock_try_acquire(struct aws_allocator *allocator, struct aws_byte_cursor instance_nonce);

/**
 * Releases the lock so the next caller (may be another process) can get an instance of the lock.
 */
AWS_COMMON_API
void aws_ipc_util_instance_lock_release(struct aws_ipc_util_instance_lock *instance_lock);

AWS_EXTERN_C_END

#endif /* #ifndef AWS_COMMON_IPC_UTIL_H */
