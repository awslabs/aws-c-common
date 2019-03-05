#include <aws/common/array_list.h>
#include <proof_helpers.h>

void aws_array_list_set_at_harness() {
    size_t initial_item_allocation = nondet_size_t();
    __CPROVER_assume(initial_item_allocation <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, initial_item_allocation, item_size);

    void *val = malloc(item_size);

    size_t index = nondet_size_t();
    __CPROVER_assume(index < __CPROVER_constant_infinity_uint - 1);

    aws_array_list_set_at(list, val, index);
}
