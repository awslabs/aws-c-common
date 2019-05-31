#include <aws/common/hash_table.h>
#include <aws/common/math.h>
#include <aws/common/private/hash_table_impl.h>
#include <aws/common/string.h>

#include <limits.h>
#include <proof_helpers/make_common_data_structures.h>
#include <proof_helpers/utils.h>
#include <stdio.h>
#include <stdlib.h>

/* Simple map for what the iterator does: it just chugs along, returns a nondet value, until its gone at most map->size
 * times */
struct aws_hash_iter aws_hash_iter_begin(const struct aws_hash_table *map) {
    /* Leave it as non-det as possible */
    AWS_PRECONDITION(aws_hash_table_is_valid(map));
    struct aws_hash_iter rval;
    rval.limit = map->p_impl->size;
    __CPROVER_assume(rval.slot <= rval.limit);
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
    return rval;
}

bool aws_hash_iter_done(const struct aws_hash_iter *iter) {
    AWS_PRECONDITION(iter->status == AWS_HASH_ITER_STATUS_DONE || iter->status == AWS_HASH_ITER_STATUS_READY_FOR_USE);
    bool rval = iter->slot == iter->limit;
    assert(rval == (iter->status == AWS_HASH_ITER_STATUS_DONE));
    return rval;
}

void aws_hash_iter_next(struct aws_hash_iter *iter) {
    if (iter->slot == iter->limit) {
        iter->status = AWS_HASH_ITER_STATUS_DONE;
        return;
    }

    struct aws_hash_iter rval;
    rval.limit = iter->limit;
    size_t next_step;
    __CPROVER_assume(next_step > 0 && next_step <= iter->limit - iter->slot);
    rval.limit = iter->limit;
    rval.slot = iter->slot + next_step;
    rval.status = (rval.slot == rval.limit) ? AWS_HASH_ITER_STATUS_DONE : AWS_HASH_ITER_STATUS_READY_FOR_USE;
    *iter = rval;
}

void aws_hash_iter_delete(struct aws_hash_iter *iter, bool destroy_contents) {
    struct aws_hash_iter rval;
    rval.slot = iter->slot;
    rval.limit = iter->limit - 1;
    rval.status = AWS_HASH_ITER_STATUS_DELETE_CALLED;
    *iter = rval;
}
