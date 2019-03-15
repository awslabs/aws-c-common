#include <aws/common/byte_buf.h>
#include <proof_helpers/make_common_data_structures.h>

void aws_byte_buf_init_harness() {
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);

    struct aws_byte_buf *buf;
    ASSUME_VALID_MEMORY(buf);

    size_t len = nondet_size_t();

    aws_byte_buf_init(buf, allocator, len);
}
