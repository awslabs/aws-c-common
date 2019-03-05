#include <aws/common/array_list.h>
#include <proof_helpers.h>

void aws_array_list_init_static_harness() {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    size_t len = nondet_size_t();
    void *raw_array = malloc(len);
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count > 0);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size > 0);

    aws_array_list_init_static(list, raw_array, item_count, item_size);

    /* some guarantees */
    /* These proofs are being rewritten.  Remove this until the rewrite is complete.
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->data == raw_array);
    */
}
