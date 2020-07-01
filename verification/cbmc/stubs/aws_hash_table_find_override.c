#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stdio.h>
#include <stdlib.h>
bool __CPROVER_file_local_hash_table_c_s_hash_keys_eq(struct hash_table_state *state, const void *a, const void *b);

int aws_hash_table_find(const struct aws_hash_table *map, const void *key, struct aws_hash_element **p_elem) {
    AWS_PRECONDITION(aws_hash_table_is_valid(map), "Input hash_table [map] must be valid.");
    AWS_PRECONDITION(AWS_OBJECT_PTR_IS_WRITABLE(p_elem), "Input pointer [p_elem] must be writable.");

    const struct hash_table_state *const state = map->p_impl;
    size_t i;

    __CPROVER_assume(i < state->size);
    if (nondet_bool()) {
        *p_elem = NULL;
    } else {
        const struct hash_table_entry *const entry = &state->slots[i];
        __CPROVER_assume(__CPROVER_file_local_hash_table_c_s_hash_keys_eq(state, key, entry->element.key));
        *p_elem = &entry->element;
    }
    AWS_POSTCONDITION(aws_hash_table_is_valid(map), "Output hash_table [map] must be valid.");
    return AWS_OP_SUCCESS;
}
