/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
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

#include <aws/common/cpuid.h>

void aws_run_cpuid(uint32_t eax, uint32_t ecx, uint32_t *abcd) {
    uint32_t ebx = 0;
    uint32_t edx = 0;

#if defined(__i386__) && defined(__PIC__)
    /* in case of PIC under 32-bit EBX cannot be clobbered */
    __asm__ __volatile__("movl %%ebx, %%edi \n\t "
                         "cpuid \n\t "
                         "xchgl %%ebx, %%edi"
                         : "=D"(ebx),
#else
    __asm__ __volatile__("cpuid"
                         : "+b"(ebx),
#endif
                           "+a"(eax),
                           "+c"(ecx),
                           "=d"(edx));
    abcd[0] = eax;
    abcd[1] = ebx;
    abcd[2] = ecx;
    abcd[3] = edx;
}
