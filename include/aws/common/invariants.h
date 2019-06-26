#ifndef AWS_COMMON_INVARIANTS_H
#define AWS_COMMON_INVARIANTS_H
/*
 * Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/assert.inl>
#include <aws/common/macros.h>

/**
 * Define function contracts.
 * When the code is being verified using CBMC these contracts are formally verified;
 * When the code is built in debug mode, they are checked as much as possible using assertions
 * When the code is built in production mode, they are not checked.
 * Violations of the function contracts are undefined behaviour.
 */
#ifdef CBMC
#    define AWS_PRECONDITION_2(cond, explanation) __CPROVER_precondition((cond), (explanation))
#    define AWS_PRECONDITION_1(cond) __CPROVER_precondition((cond), #    cond " check failed")
#    define AWS_POSTCONDITION_2(cond, explanation) __CPROVER_assert((cond), (explanation))
#    define AWS_POSTCONDITION_1(cond) __CPROVER_assert((cond), #    cond " check failed")
#    define AWS_MEM_IS_READABLE(base, len) __CPROVER_r_ok((base), (len))
#    define AWS_MEM_IS_WRITABLE(base, len) __CPROVER_w_ok((base), (len))
#else
#    define AWS_PRECONDITION_2(cond, expl) AWS_ASSERT(cond)
#    define AWS_PRECONDITION_1(cond) AWS_ASSERT(cond)
#    define AWS_POSTCONDITION_2(cond, expl) AWS_ASSERT(cond)
#    define AWS_POSTCONDITION_1(cond) AWS_ASSERT(cond)
/* the C runtime does not give a way to check these properties,
 * but we can at least check that the pointer is valid */
#    define AWS_MEM_IS_READABLE(base, len) (((len) == 0) || (base))
#    define AWS_MEM_IS_WRITABLE(base, len) (((len) == 0) || (base))
#endif /* CBMC */

// The UNUSED is used to silence the complains of GCC for zero arguments in variadic macro
#define AWS_PRECONDITION(...) GET_MACRO(__VA_ARGS__, AWS_PRECONDITION_2, AWS_PRECONDITION_1, UNUSED)(__VA_ARGS__)
#define AWS_POSTCONDITION(...) GET_MACRO(__VA_ARGS__, AWS_POSTCONDITION_2, AWS_POSTCONDITION_1, UNUSED)(__VA_ARGS__)

#define AWS_OBJECT_PTR_IS_READABLE(ptr) AWS_MEM_IS_READABLE((ptr), sizeof(*ptr))
#define AWS_OBJECT_PTR_IS_WRITABLE(ptr) AWS_MEM_IS_WRITABLE((ptr), sizeof(*ptr))

#endif /* AWS_COMMON_INVARIANTS_H */
