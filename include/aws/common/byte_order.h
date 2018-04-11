#ifndef AWS_COMMON_BYTE_ORDER_H
#define AWS_COMMON_BYTE_ORDER_H

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

#include <stdint.h>

/**
 * Returns 1 if machine is big endian, 0 if little endian.
 * If you compile with even -O1 optimization, this check is completely optimized out at compile
 * time and code which calls "if (is_big_endian())" will do the right thing without branching.
 */
static inline int is_big_endian() {
    const uint16_t z = 0x100;
    return *(const uint8_t*)&z;
}

/**
 * Swaps bytes of 64 bit integer.
 */
static inline uint64_t byteswap64(uint64_t x) { return
        (x << 56) | (x >> 56) |
        ((x & 0x0000ff00ULL) << 40) | ((x >> 40) & 0x0000ff00ULL) |
        ((x & 0x00ff0000ULL) << 24) | ((x >> 24) & 0x00ff0000ULL) |
        ((x & 0xff000000ULL) <<  8) | ((x >>  8) & 0xff000000ULL);
}

/**
 * Swaps bytes of 32 bit integer.
 */
static inline uint32_t byteswap32(uint32_t x) { return
        (x << 24) | (x >> 24) |
        ((x & 0xff00) << 8 ) | ((x >> 8) & 0xff00);
}

/**
 * Swaps bytes of 16 bit integer.
 */
static inline uint16_t byteswap16(uint16_t x) { return (x << 8) | (x >> 8); }

/**
 * Convert 64 bit integer from host to network byte order.
 */
static inline uint64_t hton64(uint64_t x) {
    if (is_big_endian()) return x;
    return byteswap64(x);
}

/**
 * Convert 64 bit integer from network to host byte order.
 */
static inline uint64_t ntoh64(uint64_t x) {
    if (is_big_endian()) return x;
    return byteswap64(x);
}

/**
 * Convert 32 bit integer from host to network byte order.
 */
static inline uint32_t hton32(uint32_t x) {
    if (is_big_endian()) return x;
    return byteswap32(x);
}

/**
 * Convert 32 bit integer from network to host byte order.
 */
static inline uint32_t ntoh32(uint32_t x) {
    if (is_big_endian()) return x;
    return byteswap32(x);
}

/**
 * Convert 16 bit integer from host to network byte order.
 */
static inline uint16_t hton16(uint16_t x) {
    if (is_big_endian()) return x;
    return byteswap16(x);
}

/**
 * Convert 16 bit integer from network to host byte order.
 */
static inline uint16_t ntoh16(uint16_t x) {
    if (is_big_endian()) return x;
    return byteswap16(x);
}

#endif /* AWS_COMMON_BYTE_ORDER_H */
