# Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

###########
include ../Makefile.aws_array_list

###########
#
# Runtime: 500s

## This is here for the backpointer array list which contains pointers
## to aws_priority_queue_node elements. As pointers are 64bits, it is
## adequate to unroll the memcpy loop twice.
UNWINDSET += memcpy_using_uint64_impl.0:2

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_using_uint64.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override_no_op.c
DEPENDENCIES += $(SRCDIR)/source/array_list.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/priority_queue.c

ABSTRACTIONS +=  $(HELPERDIR)/stubs/s_sift_either_override.c
ABSTRACTIONS +=  $(HELPERDIR)/stubs/aws_array_list_swap_override.c

ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body __CPROVER_file_local_priority_queue_c_s_sift_either
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body aws_array_list_swap_override

ENTRY = aws_priority_queue_s_remove_node_harness
###########

include ../Makefile.common
