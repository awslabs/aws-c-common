#ifndef AWS_COMMON_THREAD_SHARED_H
#define AWS_COMMON_THREAD_SHARED_H
/**
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0.
 */

#include <aws/common/common.h>

struct aws_linked_list;
struct aws_linked_list_node;

AWS_COMMON_API void aws_thread_join_and_free_wrapper_list(struct aws_linked_list *wrapper_list);
AWS_COMMON_API void aws_thread_pending_join_add(struct aws_linked_list_node *node);
AWS_COMMON_API void aws_thread_pending_join_list_swap(struct aws_linked_list *swap_list);
AWS_COMMON_API void aws_thread_initialize_thread_management(void);

#endif /* AWS_COMMON_THREAD_SHARED_H */
