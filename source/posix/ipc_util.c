/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#include <aws/common/ipc_util.h>

#include <aws/common/byte_buf.h>
#include <errno.h>
#include <sys/file.h>
#include <unistd.h>

#include <aws/common/file.h>
#include <aws/common/logging.h>

struct aws_ipc_util_instance_lock {
    struct aws_allocator *allocator;
    int locked_fd;
};

struct aws_ipc_util_instance_lock *aws_ipc_util_instance_lock_try_acquire(
    struct aws_allocator *allocator,
    struct aws_byte_cursor instance_nonce) {
    /*
     * The unix standard says /tmp has to be there and be writable. However, while it may be tempting to just use the
     * /tmp/ directory, it often has the sticky bit set which would prevent a subprocess from being able to call open
     * with create on the file. The solution is simple, just write it to a subdirectory inside
     * /tmp using the same perms as the current process.
     */
    struct aws_byte_cursor path_prefix = aws_byte_cursor_from_c_str("/tmp/crt_lock_avoid_sticky_bit/");
    struct aws_string *path_to_create = aws_string_new_from_cursor(allocator, &path_prefix);
    /* it's probably there already and we don't care if it is. The open will fail and we will handle it there
     * if we can't open it due to permissions. */
    aws_directory_create(path_to_create);
    aws_string_destroy(path_to_create);
    struct aws_byte_cursor path_suffix = aws_byte_cursor_from_c_str(".lock");

    struct aws_byte_buf nonce_buf;
    aws_byte_buf_init_copy_from_cursor(&nonce_buf, allocator, path_prefix);
    aws_byte_buf_append_dynamic(&nonce_buf, &instance_nonce);
    aws_byte_buf_append_dynamic(&nonce_buf, &path_suffix);
    aws_byte_buf_append_null_terminator(&nonce_buf);

    int fd = open((const char *)nonce_buf.buffer, O_CREAT | O_RDWR, 0666);
    if (fd < 0) {
        aws_raise_error(AWS_ERROR_NO_PERMISSION);
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s failed to open with errno %d",
            (const char *)nonce_buf.buffer,
            errno);
        aws_byte_buf_clean_up(&nonce_buf);
        return NULL;
    }
    if (flock(fd, LOCK_EX | LOCK_NB) == -1) {
        AWS_LOGF_TRACE(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s already acquired by another instance",
            (const char *)nonce_buf.buffer);
        close(fd);
        aws_byte_buf_clean_up(&nonce_buf);
        return NULL;
    }

    struct aws_ipc_util_instance_lock *instance_lock =
        aws_mem_calloc(allocator, 1, sizeof(struct aws_ipc_util_instance_lock));
    instance_lock->locked_fd = fd;
    instance_lock->allocator = allocator;

    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL,
        "static: Lock file %s acquired by this instance with fd %d",
        (const char *)nonce_buf.buffer,
        fd);
    /* we could do this once above but then we'd lose logging for the buffer. */
    aws_byte_buf_clean_up(&nonce_buf);
    return instance_lock;
}

void aws_ipc_util_instance_lock_release(struct aws_ipc_util_instance_lock *instance_lock) {
    if (instance_lock) {
        flock(instance_lock->locked_fd, LOCK_UN);
        close(instance_lock->locked_fd);
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Lock file released for fd %d", instance_lock->locked_fd);
        aws_mem_release(instance_lock->allocator, instance_lock);
    }
}
