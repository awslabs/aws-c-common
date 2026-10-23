/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */
#define _GNU_SOURCE /* NOLINT(bugprone-reserved-identifier) */ /* O_NOFOLLOW on older glibc */
#include <aws/common/cross_process_lock.h>

#include <aws/common/byte_buf.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <unistd.h>

#include <aws/common/error.h>
#include <aws/common/file.h>
#include <aws/common/logging.h>

struct aws_cross_process_lock {
    struct aws_allocator *allocator;
    int locked_fd;
};

/* rwx for everyone plus the sticky bit, same semantics as /tmp itself. */
static const mode_t s_lock_dir_mode = S_ISVTX | S_IRWXU | S_IRWXG | S_IRWXO;

/*
 * Ensures the lock directory exists, is a real directory (not a symlink), and has the sticky bit set so users can't
 * delete or replace each other's lock files.
 */
static int s_prepare_lock_dir(const char *dir_path) {
    errno = 0;
    bool created = mkdir(dir_path, s_lock_dir_mode) == 0;
    if (!created && errno != EEXIST) {
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_GENERAL, "static: Lock directory %s failed to be created with errno %d", dir_path, errno);
        /* let it fail on open of the lock file */
        return AWS_OP_SUCCESS;
    }

    /* lstat so that a pre-existing symlink is never followed. */
    struct stat dir_info;
    if (lstat(dir_path, &dir_info) != 0 || !S_ISDIR(dir_info.st_mode)) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "static: Lock directory %s is not a directory. The lock cannot be acquired.",
            dir_path);
        return aws_raise_error(AWS_ERROR_MUTEX_FAILED);
    }

    /*
     * Bypass umask on a directory we just created. On a pre-existing directory we own (e.g. created by an older version
     * without the sticky bit), only add the sticky bit. Nobody but the owner (or root) can rename a directory out of
     * the sticky /tmp, so the path still refers to the directory we just checked.
     */
    if (dir_info.st_uid == geteuid()) {
        if (created) {
            chmod(dir_path, s_lock_dir_mode);
        } else if ((dir_info.st_mode & S_ISVTX) == 0) {
            chmod(dir_path, (dir_info.st_mode & (S_IRWXU | S_IRWXG | S_IRWXO)) | S_ISVTX);
        }
    }

    return AWS_OP_SUCCESS;
}

struct aws_cross_process_lock *aws_cross_process_lock_try_acquire(
    struct aws_allocator *allocator,
    struct aws_byte_cursor instance_nonce) {

    /* validate we don't have a directory slash. */
    struct aws_byte_cursor to_find = aws_byte_cursor_from_c_str("/");
    struct aws_byte_cursor found;
    AWS_ZERO_STRUCT(found);
    if (aws_byte_cursor_find_exact(&instance_nonce, &to_find, &found) != AWS_OP_ERR &&
        aws_last_error() != AWS_ERROR_STRING_MATCH_NOT_FOUND) {
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "static: Lock " PRInSTR "creation has illegal character /",
            AWS_BYTE_CURSOR_PRI(instance_nonce));
        aws_raise_error(AWS_ERROR_INVALID_ARGUMENT);
        return NULL;
    }

    /*
     * The unix standard says /tmp has to be there and be writable. Lock files go into a dedicated world-writable
     * subdirectory with the sticky bit set, so any user can create their lock file but nobody can delete or replace
     * another user's. Opening another user's lock file with O_CREAT may fail with EACCES (e.g. due to
     * fs.protected_regular); that case falls back to opening read-only below, which is sufficient for flock().
     */
    struct aws_byte_cursor path_prefix = aws_byte_cursor_from_c_str("/tmp/aws_crt_cross_process_lock/");
    if (s_prepare_lock_dir("/tmp/aws_crt_cross_process_lock")) {
        return NULL;
    }

    struct aws_byte_cursor path_suffix = aws_byte_cursor_from_c_str(".lock");

    struct aws_byte_buf nonce_buf;
    aws_byte_buf_init_copy_from_cursor(&nonce_buf, allocator, path_prefix);
    aws_byte_buf_append_dynamic(&nonce_buf, &instance_nonce);
    aws_byte_buf_append_dynamic(&nonce_buf, &path_suffix);
    aws_byte_buf_append_null_terminator(&nonce_buf);

    struct aws_cross_process_lock *instance_lock = NULL;

    errno = 0;
    int fd = open((const char *)nonce_buf.buffer, O_CREAT | O_RDWR | O_NOFOLLOW, 0666);
    if (fd < 0) {
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s failed to open with errno %d",
            (const char *)nonce_buf.buffer,
            errno);

        aws_translate_and_raise_io_error_or(errno, AWS_ERROR_MUTEX_FAILED);

        if (aws_last_error() == AWS_ERROR_NO_PERMISSION) {
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_GENERAL,
                "static: Lock file %s couldn't be opened due to file ownership permissions. Attempting to open as read "
                "only",
                (const char *)nonce_buf.buffer);

            errno = 0;
            fd = open((const char *)nonce_buf.buffer, O_RDONLY | O_NOFOLLOW);

            if (fd < 0) {
                AWS_LOGF_ERROR(
                    AWS_LS_COMMON_GENERAL,
                    "static: Lock file %s failed to open with read-only permissions with errno %d",
                    (const char *)nonce_buf.buffer,
                    errno);
                aws_translate_and_raise_io_error_or(errno, AWS_ERROR_MUTEX_FAILED);
                goto cleanup;
            }
        } else {
            AWS_LOGF_ERROR(
                AWS_LS_COMMON_GENERAL,
                "static: Lock file %s failed to open. The lock cannot be acquired.",
                (const char *)nonce_buf.buffer);
            goto cleanup;
        }
    }

    if (flock(fd, LOCK_EX | LOCK_NB) == -1) {
        AWS_LOGF_TRACE(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s already acquired by another instance",
            (const char *)nonce_buf.buffer);
        close(fd);
        aws_raise_error(AWS_ERROR_MUTEX_CALLER_NOT_OWNER);
        goto cleanup;
    }

    instance_lock = aws_mem_calloc(allocator, 1, sizeof(struct aws_cross_process_lock));
    instance_lock->locked_fd = fd;
    instance_lock->allocator = allocator;

    AWS_LOGF_TRACE(
        AWS_LS_COMMON_GENERAL,
        "static: Lock file %s acquired by this instance with fd %d",
        (const char *)nonce_buf.buffer,
        fd);

cleanup:
    aws_byte_buf_clean_up(&nonce_buf);

    return instance_lock;
}

void aws_cross_process_lock_release(struct aws_cross_process_lock *instance_lock) {
    if (instance_lock) {
        close(instance_lock->locked_fd);
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Lock file released for fd %d", instance_lock->locked_fd);
        aws_mem_release(instance_lock->allocator, instance_lock);
    }
}
