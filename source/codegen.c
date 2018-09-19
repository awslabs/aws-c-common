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

/*
 * This file generates exportable implementations for inlineable functions.
 */

#define AWS_STATIC_IMPL AWS_COMMON_API

#include <aws/common/array_list.h>
#include <aws/common/atomics.h>
#include <aws/common/byte_buf.h>
#include <aws/common/byte_order.h>
#include <aws/common/clock.h>
#include <aws/common/common.h>
#include <aws/common/condition_variable.h>
#include <aws/common/encoding.h>
#include <aws/common/error.h>
#include <aws/common/exports.h>
#include <aws/common/hash_table.h>
#include <aws/common/linked_list.h>
#include <aws/common/lru_cache.h>
#include <aws/common/math.h>
#include <aws/common/mutex.h>
#include <aws/common/priority_queue.h>
#include <aws/common/rw_lock.h>
#include <aws/common/string.h>
#include <aws/common/system_info.h>
#include <aws/common/task_scheduler.h>
#include <aws/common/thread.h>
