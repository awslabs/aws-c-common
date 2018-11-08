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

#if AWS_SIZEOF_VOID_P == 8
typedef int64_t reader_count_t;
static const int64_t s_max_readers = INT64_MAX;
#elif AWS_SIZEOF_VOID_P == 4
typedef int32_t reader_count_t;
static const int32_t s_max_readers = INT32_MAX;
#else
#    error Unsupported pointer size
#endif

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

    return AWS_OP_ERR;
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
    assert(aws_atomic_load_int(&lock->readers) > 0);

    return AWS_OP_SUCCESS;
}

int aws_rw_lock_wlock(struct aws_rw_lock *lock) {

    aws_mutex_lock(&lock->writer_lock);

    const reader_count_t num_readers = aws_atomic_fetch_sub(&lock->readers, s_max_readers);
    if (num_readers > 0) {
        const reader_count_t num_holdouts = aws_atomic_fetch_add(&lock->holdouts, num_readers) + num_readers;
        assert(num_holdouts >= 0);
        if (num_holdouts > 0) {
            aws_semaphore_acquire(&lock->writer_sem);
        }
        assert(aws_atomic_load_int(&lock->holdouts) == 0);
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

    assert(aws_atomic_load_int(&lock->holdouts) == 0);

    const reader_count_t current = aws_atomic_fetch_add(&lock->readers, s_max_readers) + s_max_readers;
    assert(current >= 0);

    for (reader_count_t i = 0; i < current; ++i) {
        aws_semaphore_release_one(&lock->reader_sem);
    }
    aws_mutex_unlock(&lock->writer_lock);

    return AWS_OP_SUCCESS;
}
