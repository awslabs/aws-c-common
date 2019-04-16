#ifndef AWS_COMMON_WEAK_REF_H
#define AWS_COMMON_WEAK_REF_H

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
 *
 */

#include <aws/common/common.h>

struct aws_weak_ref;

/*
 * A simple API for a mutable ref-counted object reference.
 *
 * The object reference can only be used in the context of a lock-unlock pair.
 *
 * The object reference can be changed or invalidated by set.
 *
 * Acquire and release must be used to bracket the time period when a user
 * may wish to access the object referenced. _new implicitly adds a reference during creation
 *
 */
AWS_EXTERN_C_BEGIN

/*
 * Create a new weak reference.  data must initially be non-null.  The returned weak_ref has a ref count of 1.
 */
AWS_COMMON_API
struct aws_weak_ref *aws_weak_ref_new(struct aws_allocator *allocator, void *object);

/*
 * Increment the object's ref count
 */
AWS_COMMON_API
void aws_weak_ref_acquire(struct aws_weak_ref *ref);

/*
 * Decrements the object's ref count
 */
AWS_COMMON_API
void aws_weak_ref_release(struct aws_weak_ref *ref);

/*
 * Locks the weak ref and returns the contained object.  The return value should be checked for validity.
 */
AWS_COMMON_API
void *aws_weak_ref_lock(struct aws_weak_ref *ref);

/*
 * Release a lock held on the weak ref, allowing others to set or use its value.
 */
AWS_COMMON_API
void aws_weak_ref_unlock(struct aws_weak_ref *ref);

/*
 * Update the value of the object tracked by the weak ref.  Most common use will be to set the object
 * to NULL when its getting destroyed.
 */
AWS_COMMON_API
void aws_weak_ref_set(struct aws_weak_ref *ref, void *object);

AWS_EXTERN_C_END

#endif /* AWS_COMMON_WEAK_REF_H */
