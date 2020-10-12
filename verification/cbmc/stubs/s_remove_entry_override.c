#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stdio.h>
#include <stdlib.h>

/* Clears an entry. Does _not_ invoke destructor callbacks.
 * Returns the last slot touched (note that if we wrap, we'll report an index
 * lower than the original entry's index)
 */
size_t __CPROVER_file_local_hash_table_c_s_remove_entry(
    struct hash_table_state *state,
    struct hash_table_entry *entry) {
    AWS_PRECONDITION(hash_table_state_is_valid(state));
    AWS_PRECONDITION(state->entry_count > 0);
    AWS_PRECONDITION(
        entry >= &state->slots[0] && entry < &state->slots[state->size],
        "Input hash_table_entry [entry] pointer must point in the available slots.");
    state->entry_count--;

    /* This stub does not update any slots. */

    size_t index;
    __CPROVER_assume(index <= state->size);

    AWS_RETURN_WITH_POSTCONDITION(index, hash_table_state_is_valid(state) && index <= state->size);
}
