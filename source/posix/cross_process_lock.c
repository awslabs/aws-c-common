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

static const char *s_lock_dir_path = "/tmp/aws_crt_cross_process_lock";

/* rwx for everyone plus the sticky bit, same semantics as /tmp itself. */
static const mode_t s_lock_dir_mode = S_ISVTX | S_IRWXU | S_IRWXG | S_IRWXO;

/*
 * Opens the lock directory, creating it if needed, and returns a descriptor to it or -1 with an error raised.
 * The path is only resolved once, without following a symlink; everything after that goes through the descriptor, so
 * the directory can't be swapped out between checking and using it.
 */
static int s_open_lock_dir(void) {
    /* already existing is fine; any other failure surfaces when opening below. */
    mkdir(s_lock_dir_path, s_lock_dir_mode);

    int dir_fd = open(s_lock_dir_path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW);
    if (dir_fd < 0) {
        int errno_value = errno; /* Always cache errno before potential side-effect */
        AWS_LOGF_ERROR(
            AWS_LS_COMMON_GENERAL,
            "static: Lock directory %s failed to open with errno %d. The lock cannot be acquired.",
            s_lock_dir_path,
            errno_value);
        aws_translate_and_raise_io_error_or(errno_value, AWS_ERROR_MUTEX_FAILED);
        return -1;
    }

    /* Bypass umask on a directory we just created, and add the sticky bit to one created by an older version. */
    struct stat dir_info;
    if (fstat(dir_fd, &dir_info) == 0 && dir_info.st_uid == geteuid() &&
        (dir_info.st_mode & (S_ISVTX | S_IRWXU | S_IRWXG | S_IRWXO)) != s_lock_dir_mode) {
        if (fchmod(dir_fd, s_lock_dir_mode) != 0) {
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_GENERAL,
                "static: Lock directory %s failed to update permissions with errno %d",
                s_lock_dir_path,
                errno);
        }
    }

    return dir_fd;
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
    int dir_fd = s_open_lock_dir();
    if (dir_fd < 0) {
        return NULL;
    }

    struct aws_byte_cursor path_suffix = aws_byte_cursor_from_c_str(".lock");

    struct aws_byte_buf nonce_buf;
    aws_byte_buf_init_copy_from_cursor(&nonce_buf, allocator, instance_nonce);
    aws_byte_buf_append_dynamic(&nonce_buf, &path_suffix);
    aws_byte_buf_append_null_terminator(&nonce_buf);

    struct aws_cross_process_lock *instance_lock = NULL;

    errno = 0;
    int fd = openat(dir_fd, (const char *)nonce_buf.buffer, O_CREAT | O_RDWR | O_NOFOLLOW, 0666);
    if (fd < 0) {
        AWS_LOGF_DEBUG(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s/%s failed to open with errno %d",
            s_lock_dir_path,
            (const char *)nonce_buf.buffer,
            errno);

        aws_translate_and_raise_io_error_or(errno, AWS_ERROR_MUTEX_FAILED);

        if (aws_last_error() == AWS_ERROR_NO_PERMISSION) {
            AWS_LOGF_DEBUG(
                AWS_LS_COMMON_GENERAL,
                "static: Lock file %s/%s couldn't be opened due to file ownership permissions. Attempting to open as "
                "read only",
                s_lock_dir_path,
                (const char *)nonce_buf.buffer);

            errno = 0;
            fd = openat(dir_fd, (const char *)nonce_buf.buffer, O_RDONLY | O_NOFOLLOW);

            if (fd < 0) {
                AWS_LOGF_ERROR(
                    AWS_LS_COMMON_GENERAL,
                    "static: Lock file %s/%s failed to open with read-only permissions with errno %d",
                    s_lock_dir_path,
                    (const char *)nonce_buf.buffer,
                    errno);
                aws_translate_and_raise_io_error_or(errno, AWS_ERROR_MUTEX_FAILED);
                goto cleanup;
            }
        } else {
            AWS_LOGF_ERROR(
                AWS_LS_COMMON_GENERAL,
                "static: Lock file %s/%s failed to open. The lock cannot be acquired.",
                s_lock_dir_path,
                (const char *)nonce_buf.buffer);
            goto cleanup;
        }
    }

    if (flock(fd, LOCK_EX | LOCK_NB) == -1) {
        AWS_LOGF_TRACE(
            AWS_LS_COMMON_GENERAL,
            "static: Lock file %s/%s already acquired by another instance",
            s_lock_dir_path,
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
        "static: Lock file %s/%s acquired by this instance with fd %d",
        s_lock_dir_path,
        (const char *)nonce_buf.buffer,
        fd);

cleanup:
    aws_byte_buf_clean_up(&nonce_buf);
    close(dir_fd);

    return instance_lock;
}

void aws_cross_process_lock_release(struct aws_cross_process_lock *instance_lock) {
    if (instance_lock) {
        close(instance_lock->locked_fd);
        AWS_LOGF_TRACE(AWS_LS_COMMON_GENERAL, "static: Lock file released for fd %d", instance_lock->locked_fd);
        aws_mem_release(instance_lock->allocator, instance_lock);
    }
}
