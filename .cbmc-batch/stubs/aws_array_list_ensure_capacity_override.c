#include <aws/common/array_list.h>

int aws_array_list_ensure_capacity(struct aws_array_list *AWS_RESTRICT list, size_t index) {
    AWS_PRECONDITION(aws_array_list_is_valid(list));
    size_t necessary_size;
    if (aws_array_list_calc_necessary_size(list, index, &necessary_size)) {
        AWS_POSTCONDITION(aws_array_list_is_valid(list));
        return AWS_OP_ERR;
    }

    if (list->current_size < necessary_size) {
        if (!list->alloc) {
            AWS_POSTCONDITION(aws_array_list_is_valid(list));
            return aws_raise_error(AWS_ERROR_INVALID_INDEX);
        }
        list->data = bounded_malloc(necessary_size);
        list->current_size = necessary_size;
    }

    AWS_POSTCONDITION(aws_array_list_is_valid(list));
    return AWS_OP_SUCCESS;
}
