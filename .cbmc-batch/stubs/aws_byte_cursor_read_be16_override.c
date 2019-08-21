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

#include <aws/common/byte_buf.h>
#include <proof_helpers/nondet.h>

/**
 * The signature for the value generator, if it is used.
 */
#ifdef AWS_BYTE_CURSOR_READ_BE16_GENERATOR
uint16_t AWS_BYTE_CURSOR_READ_BE16_GENERATOR(const struct aws_byte_cursor *cursor);
#endif

/**
 * This function is used in deserializing values from a byte cursor.
 * Sometimes, for CBMC proof, it is expected that certain values in byte stream are constrained.
 * For example, in the aws_cryptosdk_enc_ctx_deserilize() proof, the first value we read is the number of elements,
 * which we need to be constrained in order to ensure that CBMC can fully unwind all loops. All other values can be left
 * nondet. In this case, define -DAWS_BYTE_CURSOR_READ_BE16_GENERATOR=generator_name, and the correct generator will be
 * called. If there is no structure that must be followed, AWS_BYTE_CURSOR_READ_BE16_GENERATOR can be left undefined,
 * and the var will be set to a nondet value.
 */
bool aws_byte_cursor_read_be16(struct aws_byte_cursor *cursor, uint16_t *var) {
    AWS_PRECONDITION(aws_byte_cursor_is_valid(cursor));
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(var));

#ifdef AWS_BYTE_CURSOR_READ_BE16_GENERATOR
    *var = AWS_BYTE_CURSOR_READ_BE16_GENERATOR(cursor);
#else
    *var = nondet_uint16_t();
#endif

    const size_t len = sizeof(uint16_t);
    /* If there are not 2 bytes left, or if we nondet fail */
    if (cursor->len > (SIZE_MAX >> 1) || len > (SIZE_MAX >> 1) || len > cursor->len || nondet_bool()) {
        AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
        return false;
    }

    /* Otherwise, succeed */
    cursor->ptr += len;
    cursor->len -= len;
    AWS_POSTCONDITION(aws_byte_cursor_is_valid(cursor));
    return true;
}
