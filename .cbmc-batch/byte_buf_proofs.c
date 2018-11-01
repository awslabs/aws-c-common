#include <aws/common/byte_buf.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <proof_helpers.h>

#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

void aws_byte_buf_init_verify(void) {
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);

    struct aws_byte_buf *buf;
    ASSUME_VALID_MEMORY(buf);

    size_t len = nondet_size_t();

    aws_byte_buf_init(buf, allocator, len);
}

void aws_byte_buf_from_c_str_verify(void) {
    size_t len = nondet_size_t();

    char *c_str;
    ASSUME_VALID_MEMORY_COUNT(c_str, len);

    /* Need *c_str to be a '\0'-terminated C string, so assume an arbitrary character is 0 */
    int index = nondet_int();
    __CPROVER_assume(index >= 0 && index < len);
    c_str[index] = 0;

    /* Assume the length of the string is bounded by some max length */
    __CPROVER_assume(len <= MAX_STR_LEN);

    aws_byte_buf_from_c_str(c_str);
}

void aws_byte_buf_append_verify(void) {
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
