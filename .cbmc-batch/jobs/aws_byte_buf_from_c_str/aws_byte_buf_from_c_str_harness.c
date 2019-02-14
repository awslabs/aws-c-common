#include <aws/common/byte_buf.h>
#include <proof_helpers.h>

void aws_byte_buf_from_c_str_harness() {
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
