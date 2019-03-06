#include<stdlib.h>

#define MAX_INITIAL_ITEM_ALLOCATION 2
#define MAX_ITEM_SIZE 15
#define MAX_STR_LEN 32
#define MAX_BUF_LEN 32

#define ASSUME_VALID_MEMORY(ptr) ptr = malloc(sizeof(*(ptr)))
#define ASSUME_VALID_MEMORY_COUNT(ptr, count) ptr = malloc(sizeof(*(ptr)) * (count))
#define ASSUME_DEFAULT_ALLOCATOR(allocator) allocator = aws_default_allocator()
#define ASSUME_ARBITRARY_ARRAY_LIST(list, item_count, item_size) list = get_arbitrary_array_list( (item_count), (item_size) )

int nondet_int();
size_t nondet_size_t();

struct aws_array_list *get_arbitrary_array_list(size_t item_count, size_t item_size) {
    struct aws_array_list *list;
    /* Assume list is allocated */
    ASSUME_VALID_MEMORY(list);

    if (nondet_int()) { /* Dynamic initialization */
        /* Use default allocator */
        struct aws_allocator *allocator = malloc(sizeof(*allocator));
        ASSUME_DEFAULT_ALLOCATOR(allocator);
        __CPROVER_assume(!aws_array_list_init_dynamic(list, allocator, item_count, item_size));
    } else { /* Static initialization */
        __CPROVER_assume(item_count > 0);
        __CPROVER_assume(item_size > 0);

        size_t len = item_count * item_size;
        void *raw_array = malloc(len);

        aws_array_list_init_static(list, raw_array, item_count, item_size);
    }

    return list;
}
