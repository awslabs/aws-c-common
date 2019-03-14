/*
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *     http://aws.amazon.com/apache2.0/
 *
 * or in the "license" file accompanying this file. This file is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#pragma once

#include <aws/common/array_list.h>
#include <aws/common/common.h>

#include "nondet.h"

#include <stdlib.h>

#define MAX_INITIAL_ITEM_ALLOCATION 2
#define MAX_ITEM_SIZE 2
#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

#define ASSUME_VALID_MEMORY(ptr) ptr = malloc(sizeof(*(ptr)))
#define ASSUME_VALID_MEMORY_COUNT(ptr, count) ptr = malloc(sizeof(*(ptr)) * (count))
#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()
#define ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size)                                                       \
    list = make_arbitrary_array_list((item_count), (item_size))

struct aws_array_list *make_arbitrary_array_list(size_t item_count, size_t item_size);
