#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_append_harness() {
    size_t len1 = nondet_size_t();
    __CPROVER_assume(len1 <= MAX_BUF_LEN);
    size_t len2 = nondet_size_t();

    /* Need arbitrary buf that is "correct enough" */
    struct aws_byte_buf *to;
    ASSUME_VALID_MEMORY(to);
    ASSUME_VALID_MEMORY_COUNT(to->buffer, len1);
    to->capacity = len1;
    __CPROVER_assume(to->len <= to->capacity);

    /* Need arbitrary cursor */
    struct aws_byte_cursor *from;
    ASSUME_VALID_MEMORY(from);
    from->ptr = malloc(len2);
    __CPROVER_assume(from->len <= len2);

    aws_byte_buf_append(to, from);
}
