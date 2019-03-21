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

#include <stddef.h>

/** Abstract memcmp to check that pointers are valid, and then return nondet */


int memcmp(const void *s1, const void *s2, size_t n)
{
  //  __CPROVER_HIDE:;
  int res=0;
  __CPROVER_precondition(__CPROVER_r_ok(s1, n),
                         "memcmp region 1 readable");
  __CPROVER_precondition(__CPROVER_r_ok(s2, n),
                         "memcpy region 2 readable");

#if 1
  const unsigned char *sc1=s1, *sc2=s2;
  for(; n!=0; n--)
  {
    res = (*sc1++) - (*sc2++);
    if (res != 0)
    return res;
  }
  return res;
#else
  return nondet_int();
#endif
}
