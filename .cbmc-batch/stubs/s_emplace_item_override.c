#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stdio.h>
#include <stdlib.h>

/**
 * Attempts to locate an element at key. If no such element was found,
 * creates a new element, with value initialized to NULL. In either case, a
 * pointer to the element is placed in *p_elem.
 *
 * If was_created is non-NULL, *was_created is set to 0 if an existing
 * element was found, or 1 is a new element was created.
 *
 * Returns AWS_OP_SUCCESS if an item was found or created.
 * Raises AWS_ERROR_OOM if hash table expansion was required and memory
 * allocation failed.
 */

struct hash_table_entry *__CPROVER_file_local_hash_table_c_s_emplace_item(
    struct hash_table_state *state,
    struct hash_table_entry entry,
    size_t probe_idx) {
    AWS_PRECONDITION(hash_table_state_is_valid(state), "Input hash_table_state [state] must be valid.");

    if (entry.hash_code == 0) {
        AWS_POSTCONDITION(hash_table_state_is_valid(state), "Output hash_table_state [state] must be valid.");
        return NULL;
    }

    size_t index;
    __CPROVER_assume(index < state->size);
    __CPROVER_assume(state->slots[index].hash_code == 0);
    state->slots[index] = entry;
    size_t empty_slot_idx;
    __CPROVER_assume(hash_table_state_has_an_empty_slot(state, &empty_slot_idx));
    AWS_POSTCONDITION(hash_table_state_is_valid(state), "Output hash_table_state [state] must be valid.");
    return &state->slots[index];
}
