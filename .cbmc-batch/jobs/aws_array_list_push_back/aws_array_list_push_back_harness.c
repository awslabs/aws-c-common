#include <aws/common/array_list.h>
#include <proof_helpers.h>

void aws_array_list_push_back_harness() {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    aws_array_list_push_back(list, val);
}
