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
#include <aws/common/device_random.h>

#include <bcrypt.h>

static HANDLE s_alg_handle = NULL;
static aws_thread_once s_rand_init = AWS_THREAD_ONCE_INIT;

static void s_init_rand(void) {
    NTSTATUS status = 0;

    status = BCryptOpenAlgorithmProvider(&s_alg_handle, BCRYPT_RNG_ALGORITHM, NULL, 0);

    if (!NT_SUCCESS(status)) {
        return abort();
    }
}

int aws_device_random_buffer(struct aws_byte_buf *output) {

    size_t diff = output->capacity - output->len;
    status = BCryptGenRandom(m_algHandle, output->buffer + output->len, diff, 0);

    if (!NT_SUCCESS(status)) {
        return aws_raise_error(AWS_ERROR_RANDOM_GEN_FAILED);
    }

    output->len += diff;
    return AWS_OP_SUCCESS;
}
