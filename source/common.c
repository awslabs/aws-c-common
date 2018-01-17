/*
* Copyright 2010-2017 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/common.h>
#include <stdlib.h>

void *default_malloc(struct aws_allocator *allocator, size_t size) {
    return malloc(size);
}

void default_free(struct aws_allocator *allocator, void *ptr) {
    free(ptr);
}

static struct aws_allocator default_allocator = {
        .mem_acquire = default_malloc,
        .mem_release = default_free
};

struct aws_allocator *aws_default_allocator() {
    return &default_allocator;
}

void *aws_mem_acquire(struct aws_allocator *allocator, size_t size) {
    return allocator->mem_acquire(allocator, size);
}

void aws_mem_release(struct aws_allocator *allocator, void *ptr) {
    allocator->mem_release(allocator, ptr);
}

static int8_t error_strings_loaded = 0;

static struct aws_error_info errors[] = {
        AWS_DEFINE_ERROR_INFO(aws_error_success, AWS_ERROR_SUCCESS, "success", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_oom, AWS_ERROR_OOM, "out-of-memory", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_invalid_buffer_size, AWS_ERROR_INVALID_BUFFER_SIZE, "invalid buffer size", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_invalid_hex_str, AWS_ERROR_INVALID_HEX_STR, "invalid hex string", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_invalid_index, AWS_ERROR_INVALID_INDEX, "invalid index for list access", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_list_empty, AWS_ERROR_LIST_EMPTY, "empty list", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_list_dest_copy_too_small, AWS_ERROR_LIST_DEST_COPY_TOO_SMALL, "destination of list copy is too small", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_list_exceeds_max_size, AWS_ERROR_LIST_EXCEEDS_MAX_SIZE, "a requested operation on a list would exceed it's max size.", AWS_LIB_NAME),
        AWS_DEFINE_ERROR_INFO(aws_error_list_static_mode_cant_shrink, AWS_ERROR_LIST_STATIC_MODE_CANT_SHRINK, "attempt to shrink a list in static mode", AWS_LIB_NAME),
};

static struct aws_error_info_list list = {
       .error_list = errors,
        .count = sizeof(errors) / sizeof(struct aws_error_info),
};

void aws_load_error_strings(void) {
    if(!error_strings_loaded) {
        error_strings_loaded = 1;
        aws_register_error_info(&list);
    }
}
