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

#if defined(__GNUC__) || defined(__clang__)

    inline int aws_atomic_get(int *dst) {
        int value;
        do {
            value = *dst;
        } while (!aws_atomic_compare_exchange(dst, value, value));
        return value;
    }

    inline int aws_atomic_set(int *dst, int value) {
        return __sync_lock_test_and_set(dst, value);
    }

    inline int aws_atomic_add(int *dst, int addend) {
        return __sync_fetch_and_add(dst, addend);
    }

    inline int aws_atomic_compare_exchange(int *dst, int compare, int value) {
        return __sync_bool_compare_and_swap(dst, compare, value);
    }

    inline void *aws_atomic_get_ptr(void **dst) {
        void *value;
        do {
            value = *dst;
        } while (!aws_atomic_compare_exchange_ptr(dst, value, value));
        return value;
    }

    void *aws_atomic_set_ptr(void **dst, void *value) {
        return __sync_lock_test_and_set(dst, value);
    }

    inline int aws_atomic_compare_exchange_ptr(void **dst, void *compare, void *value) {
        return __sync_bool_compare_and_swap(dst, compare, value);
    }

#elif defined _WIN32

    /* These definitions reside in atomics.c to avoid extraneous header inclusions. */

#else

    #error Unsupported platform for atomics.

#endif
