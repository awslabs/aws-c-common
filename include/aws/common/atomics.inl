#ifndef AWS_COMMON_ATOMICS_INL
#define AWS_COMMON_ATOMICS_INL

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

#define AWS_ATOMICS_INLINE

#include <aws/common/atomics.h>

/* Helpers for converting aws_atomic_var into its parts. */
#define AWS_ATOMIC_VAR_PTRVAL(var) (var->value)
#define AWS_ATOMIC_VAR_INTVAL(var) (*(aws_atomic_impl_int_t *)var)

/* Include the backend implementation now, because we'll use its typedefs and #defines below */
#if defined(__GNUC__) || defined(__clang__)

#    if defined(__ATOMIC_RELAXED)

#        include <aws/common/atomics_gnu.inl>

#    else

#        include <aws/common/atomics_gnu_old.inl>

#    endif /* __ATOMIC_RELAXED */

#elif defined(_MSC_VER)

#    include <aws/common/atomics_msvc.inl>

#else

#    error No atomics implementation for your compiler is available

#endif

#include <aws/common/atomics_fallback.inl>

/* If these fail, the size of aws_atomic_var needs to be increased. */
AWS_STATIC_ASSERT(sizeof(struct aws_atomic_var) >= sizeof(aws_atomic_impl_int_t));
AWS_STATIC_ASSERT(sizeof(struct aws_atomic_var) >= sizeof(void *));

#endif /* AWS_COMMON_ATOMICS_INL */
