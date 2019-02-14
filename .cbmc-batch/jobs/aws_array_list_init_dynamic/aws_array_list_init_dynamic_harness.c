#include <aws/common/array_list.h>
#include <proof_helpers.h>

void aws_array_list_init_dynamic_harness() {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);
    size_t item_count = nondet_size_t();
    size_t item_size = nondet_size_t();

    aws_array_list_init_dynamic(list, allocator, item_count, item_size);

    /* some guarantees */
    /* These proofs are being rewritten.  Remove this until the rewrite is complete.
    assert(list->alloc == allocator);
    assert(list->item_size == item_size);
    if (item_count <= MAX_INITIAL_ITEM_ALLOCATION && item_size <= MAX_ITEM_SIZE)
        assert(list->data == NULL || list->current_size == (item_count * item_size));
    */
}
