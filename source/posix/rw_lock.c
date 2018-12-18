/*
 * Copyright 2010-2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#include <aws/common/config.h>
#include <aws/common/rw_lock.h>

#include <aws/common/posix/common.inl>

#include <assert.h>

#if SIZE_MAX == UINT64_MAX
typedef int64_t reader_count_t;
static const int64_t s_max_readers = INT64_MAX;
#elif SIZE_MAX == UINT32_MAX
typedef int32_t reader_count_t;
static const int32_t s_max_readers = INT32_MAX;
#else
#    error Unsupported pointer size
#endif

/**
 * Some notes about the implementation of this structure:
 *  1. lock->writer_lock exists to ensure only 1 writer is active at a time. It will be locked from wlock to wunlock.
 *  2. lock->readers will be equal to the number of open readers when > 0,
 *      and (the number of open readers - s_max_readers) when a writer is waiting.
 *  3. lock->holdouts refers to the number of readers that were open when a writer attempted to obtain the lock.
 *      Calls to runlock will decrement this count as well as lock->readers,
 *      and once holdouts reaches 0, lock->writer_sem will be released and the writer will commence.
 *  4. lock->reader_sem will be released when the writer is done and the readers may commence.
 */

int aws_rw_lock_init(struct aws_rw_lock *lock) {

    aws_atomic_init_int(&lock->readers, 0);
    aws_atomic_init_int(&lock->holdouts, 0);
    if (aws_semaphore_init(&lock->reader_sem, 0, s_max_readers)) {
        return AWS_OP_ERR;
    }
    if (aws_semaphore_init(&lock->writer_sem, 0, 1)) {
        aws_semaphore_clean_up(&lock->reader_sem);
        return AWS_OP_ERR;
    }
    if (aws_mutex_init(&lock->writer_lock)) {
        aws_semaphore_clean_up(&lock->reader_sem);
        aws_semaphore_clean_up(&lock->writer_sem);
        return AWS_OP_ERR;
    }

    return AWS_OP_SUCCESS;
}

void aws_rw_lock_clean_up(struct aws_rw_lock *lock) {

    aws_semaphore_clean_up(&lock->reader_sem);
    aws_semaphore_clean_up(&lock->writer_sem);
    aws_mutex_clean_up(&lock->writer_lock);
}

int aws_rw_lock_rlock(struct aws_rw_lock *lock) {

    const reader_count_t num_readers = aws_atomic_fetch_add(&lock->readers, 1) + 1;
    if (num_readers < 0) {
        aws_semaphore_acquire(&lock->reader_sem);
    }

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    aws_mutex_lock(&lock->writer_lock);

    const reader_count_t num_readers = aws_atomic_fetch_sub(&lock->readers, s_max_readers);
    if (num_readers != 0) {
        const reader_count_t num_holdouts = aws_atomic_fetch_add(&lock->holdouts, num_readers) + num_readers;
        if (num_holdouts > 0) {
            aws_semaphore_acquire(&lock->writer_sem);
        }
    }

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_runlock(struct aws_rw_lock *lock) {

    const reader_count_t num_readers = aws_atomic_fetch_sub(&lock->readers, 1) - 1;

    if (num_readers < 0) {
        const reader_count_t num_holdouts = aws_atomic_fetch_sub(&lock->holdouts, 1) - 1;
        if (num_holdouts == 0) {
            aws_semaphore_release_one(&lock->writer_sem);
        }
    }

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wunlock(struct aws_rw_lock *lock) {

    const reader_count_t current = aws_atomic_fetch_add(&lock->readers, s_max_readers) + s_max_readers;

    aws_semaphore_release(&lock->reader_sem, current);
    aws_mutex_unlock(&lock->writer_lock);

    return AWS_OP_SUCCESS;
}
