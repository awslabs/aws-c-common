#include <aws/common/array_list.h>
#include <assert.h>
#include <stddef.h>
#include <string.h>
#include <stdlib.h>
#include <stdarg.h>
#include <proof_helpers.h>

#define MAX_INITIAL_ITEM_ALLOCATION 2
#define MAX_ITEM_SIZE 15

void aws_array_list_init_dynamic_verify(void) {
    struct aws_array_list *list;
    ASSUME_VALID_MEMORY(list);
    struct aws_allocator *allocator;
    ASSUME_DEFAULT_ALLOCATOR(allocator);
    size_t item_count = nondet_size_t();
    size_t item_size = nondet_size_t();

    aws_array_list_init_dynamic(list, allocator, item_count, item_size);
    
    /* some guarantees */
    assert(list->alloc == allocator);
    assert(list->item_size == item_size);
    if (item_count <= MAX_INITIAL_ITEM_ALLOCATION && item_size <= MAX_ITEM_SIZE)
        assert(list->data == NULL || list->current_size == (item_count * item_size));
}

void aws_array_list_init_static_verify(void) {
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
    assert(list->alloc == NULL);
    assert(list->item_size == item_size);
    assert(list->data == raw_array);
}

void aws_array_list_set_at_verify(void) {
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

void aws_array_list_push_back_verify(void) {
    size_t item_count = nondet_size_t();
    __CPROVER_assume(item_count <= MAX_INITIAL_ITEM_ALLOCATION);
    size_t item_size = nondet_size_t();
    __CPROVER_assume(item_size <= MAX_ITEM_SIZE);
    struct aws_array_list *list;
    ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size);

    void *val = malloc(item_size);

    aws_array_list_push_back(list, val);
}
