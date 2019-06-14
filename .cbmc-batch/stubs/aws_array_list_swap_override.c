/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

/**
 * FUNCTION: aws_array_list_swap
 *
 * We override aws_array_list_swap because mem_swap makes CBMC
 * struggle (because of the many memcpys) and because the
 * array_list_get_at in before the mem_swap are unneccessary if we
 * stub out mem_swap. Instead we add a havoc assertion on the two
 * swapped byted to ensure that no assertion on the values of the two
 * cells is made afterwards.
 */

#include <aws/common/array_list.h>

void aws_array_list_swap(struct aws_array_list *AWS_RESTRICT list, size_t a, size_t b) {
    assert(a < list->length);
    assert(b < list->length);
    assert(aws_array_list_is_valid(list));

    return;
}
