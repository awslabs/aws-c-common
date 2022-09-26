#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stdio.h>
#include <stdlib.h>

/* If the consumer of the iterator doesn't use the .element in the iterator, we can just leave it undef
 * This is sound, as it gives you a totally nondet value every time you call the iterator, and is the default behaviour
 * of CBMC. But if it is used, we need a way for the harness to specify valid values for the element, for example if
 * they are copying values out of the table. They can do this by defining
 * -DHASH_ITER_ELEMENT_GENERATOR=the_generator_fn, where the_generator_fn has signature:
 *   the_generator_fn(struct aws_hash_iter *new_iter, const struct aws_hash_iter* old_iter).
 *
 * [new_iter] is a pointer to the iterator that will be returned from this function, and the generator function can
 * modify it in any way it sees fit.  In particular, it can update the [new_iter->element] field to be valid for the
 * type of hash-table being proved.  Two obvious generators are:
 *   (a) one that simply creates a new non-determinsitic value each time its called using malloc
 *   (b) one that uses a value stored in the underlying map, and copies it into the iterator.
 *
 * [old_iter] is a pointer to the old iterator, in the case of a "aws_hash_iter_next" call, and null in the case of
 * "aws_hash_iter_begin".
 */
#ifdef HASH_ITER_ELEMENT_GENERATOR
void HASH_ITER_ELEMENT_GENERATOR(struct aws_hash_iter *new_iter, const struct aws_hash_iter *old_iter);
#endif

/* Simple map for what the iterator does: it just chugs along, returns a nondet value, until its gone at most map->size
 * times */
struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map) {
    /* Leave it as non-det as possible */
    AWS_PRECONDITION(aws_hash_table_is_valid(map));

    /* Build a nondet iterator, set the required fields, and return it */
    struct aws_hash_iter rval;
    rval.map = map;
    rval.limit = map->p_impl->size;
    __CPROVER_assume(rval.slot <= rval.limit);
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
#ifdef HASH_ITER_ELEMENT_GENERATOR
    HASH_ITER_ELEMENT_GENERATOR(&rval, NULL);
#endif
    return rval;
}

bool aws_hash_iter_done(const struct aws_hash_iter *iter) {
    AWS_PRECONDITION(
        iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE,
        "Input aws_hash_iter [iter] status should either be done or ready to use.");
    bool rval = iter->slot == iter->limit;
    assert(rval == (iter->status == AWS_HASH_ITER_STATUS_DONE));
    return rval;
}

void aws_hash_iter_next(struct aws_hash_iter *iter) {
    if (iter->slot == iter->limit) {
        iter->status = AWS_HASH_ITER_STATUS_DONE;
        return;
    }

    /* Build a nondet iterator, set the required fields, and copy it over */
    struct aws_hash_iter rval;
    rval.map = iter->map;
    rval.limit = iter->limit;
    size_t next_step;
    __CPROVER_assume(next_step > 0 && next_step <= iter->limit - iter->slot);
    rval.limit = iter->limit;
    rval.slot = iter->slot + next_step;
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
#ifdef HASH_ITER_ELEMENT_GENERATOR
    HASH_ITER_ELEMENT_GENERATOR(&rval, iter);
#endif

    *iter = rval;
}

/* delete always leaves the element unusable, so we'll just leave the element totally nondet */
void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents) {
    /* Build a nondet iterator, set the required fields, and copy it over */
    struct aws_hash_iter rval;
    rval.map = iter->map;
    rval.slot = iter->slot;
    rval.limit = iter->limit - 1;
    rval.status = AWS_HASH_ITER_STATUS_DELETE_CALLED;
    rval.map->p_impl->entry_count = iter->map->p_impl->entry_count;
    if (rval.map->p_impl->entry_count)
        rval.map->p_impl->entry_count--;
    *iter = rval;
}
