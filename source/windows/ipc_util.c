/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <windows.h>

#include <aws/common/byte_buf.h>
#include <aws/common/ipc_util.h>
#include <aws/common/logging.h>
#include <inttypes.h>

struct aws_ipc_util_instance_lock {
    struct aws_allocator *allocator;
    HANDLE mutex;
};

struct aws_ipc_util_instance_lock *aws_ipc_util_instance_lock_try_acquire(
    struct aws_allocator *allocator,
    struct aws_byte_cursor instance_nonce) {

    /* validate we don't have a directory slash. */
    struct aws_byte_cursor to_find = aws_byte_cursor_from_c_str("\\");
    struct aws_byte_cursor found;
    AWS_ZERO_STRUCT(found);
    if (aws_byte_cursor_find_exact(&instance_nonce, &to_find, &found) != AWS_OP_ERR &&
        aws_last_error() != AWS_ERROR_STRING_MATCH_NOT_FOUND) {
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    struct aws_byte_cursor path_prefix = aws_byte_cursor_from_c_str("Global/");
    struct aws_byte_buf nonce_buf;
    aws_byte_buf_init_copy_from_cursor(&nonce_buf, allocator, path_prefix);
    aws_byte_buf_append_dynamic(&nonce_buf, &instance_nonce);
    aws_byte_buf_append_null_terminator(&nonce_buf);

    HANDLE mutex = CreateMutexA(NULL, FALSE, (LPCSTR)nonce_buf.buffer);

    if (!mutex) {
        AWS_LOGF_WARN(
            AWS_LS_COMMON_GENERAL,
            "static: Lock %s creation failed with error %" PRIx32,
            (const char *)nonce_buf.buffer,
            GetLastError());
        aws_byte_buf_clean_up(&nonce_buf);
    }

    /* from the docs:
     * If the mutex is a named mutex and the object existed before this function call, the return value is a handle
     * to the existing object, and the GetLastError function returns ERROR_ALREADY_EXISTS. */
    if (GetLastError() == ERROR_ALREADY_EXISTS) {
        AWS_LOGF_TRACE(
            AWS_LS_COMMON_GENERAL,
            "static: Lock %s is already acquired by another  instance",
            (const char *)nonce_buf.buffer,
            (void *)mutex);
        CloseHandle(mutex);
        aws_byte_buf_clean_up(&nonce_buf);
        return NULL;
    }

    struct aws_ipc_util_instance_lock *instance_lock =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_ipc_util_instance_lock));
    instance_lock->mutex = mutex;
    instance_lock->allocator = allocator;

    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL,
        "static: Lock %s acquired by this instance with HANDLE %p",
        (const char *)nonce_buf.buffer,
        (void *)mutex);
    /* we could do this once above but then we'd lose logging for the buffer. */
    aws_byte_buf_clean_up(&nonce_buf);
    return instance_lock;
}

void aws_ipc_util_instance_lock_release(struct aws_ipc_util_instance_lock *instance_lock) {
    if (instance_lock) {
        CloseHandle(instance_lock->mutex);
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Lock file released for handle %p", (void *)instance_lock->mutex);
        aws_mem_release(instance_lock->allocator, instance_lock);
    }
}
