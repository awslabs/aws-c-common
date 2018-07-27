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

    static inline int aws_atomic_load(int *dst) {
        return __sync_val_compare_and_swap(dst, 0, 0);
    }

    static inline int aws_atomic_store(int *dst, int value) {
        return __sync_lock_test_and_set(dst, value);
    }

    static inline int aws_atomic_add(int *dst, int addend) {
        return __sync_fetch_and_add(dst, addend);
    }

    static inline bool aws_atomic_compare_exchange(int *dst, int *compare, int value) {
        int comp = *compare;
        int ret = __sync_val_compare_and_swap(dst, comp, value);
        if (ret == comp) {
            return true;
        } else {
            *compare = ret;
            return false;
        }
    }

    static inline void *aws_atomic_load_ptr(void **dst) {
        return __sync_val_compare_and_swap(dst, 0, 0);
    }

    static inline void *aws_atomic_store_ptr(void **dst, void *value) {
        return __sync_lock_test_and_set(dst, value);
    }

    static inline bool aws_atomic_compare_exchange_ptr(void **dst, void **compare, void *value) {
        void *comp = *compare;
        void *ret = __sync_val_compare_and_swap(dst, comp, value);
        if (ret == comp) {
            return true;
        } else {
            *compare = ret;
            return false;
        }
    }

#elif defined _WIN32

    #include <intrin.h>

    static inline int aws_atomic_load(int *dst) {
        return _InterlockedCompareExchange((long*)dst, 0, 0);
    }

    static inline int aws_atomic_store(int *dst, int value) {
        return _InterlockedExchange((long *)dst, value);
    }

    static inline int aws_atomic_add(int *dst, int addend) {
        return (int)_InterlockedExchangeAdd((long *)dst, (long)addend);
    }

    static inline bool aws_atomic_compare_exchange(int *dst, int *compare, int value) {
        long comp = (long)*compare;
        long ret = _InterlockedCompareExchange((long *)dst, (long)value, comp);
        if (ret == comp) {
            return true;
        } else {
            *(long *)compare = ret;
            return false;
        }
    }

    static inline void *aws_atomic_load_ptr(void **dst) {
        return _InterlockedCompareExchangePointer(dst, 0, 0);
    }

    static inline void *aws_atomic_store_ptr(void **dst, void *value) {
        return _InterlockedExchangePointer(dst, value);
    }

    static inline bool aws_atomic_compare_exchange_ptr(void **dst, void **compare, void *value) {
        void *comp = *compare;
        void *ret = _InterlockedCompareExchangePointer(dst, value, comp);
        if (ret == comp) {
            return true;
        } else {
            *compare = ret;
            return false;
        }
    }

#else

    #error Unsupported platform for atomics.

#endif
