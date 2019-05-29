
#include <aws/common/priority_queue.h>

bool __CPROVER_file_local_priority_queue_c_s_sift_up(struct aws_priority_queue *queue, size_t index) {
    AWS_PRECONDITION(aws_priority_queue_is_valid(queue));
    AWS_PRECONDITION(index < queue->container.length);
    bool did_move;
    AWS_POSTCONDITION(aws_priority_queue_is_valid(queue));
    return did_move;
}
