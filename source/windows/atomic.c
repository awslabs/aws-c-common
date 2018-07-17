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

#include <intrin.h>

int aws_atomic_cas(int *dst, int compare, int value) {
    return _InterlockedCompareExchange((long *)dst, (long)value, (long)compare) == (long)compare;
}

int aws_atomic_cas_ptr(void **dst, void *compare, void *value) {
    return _InterlockedCompareExchangePointer(dst, value, compare) == compare;
}
