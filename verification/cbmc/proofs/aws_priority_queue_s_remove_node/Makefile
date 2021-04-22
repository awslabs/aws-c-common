# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

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

PROOF_UID = aws_priority_queue_s_remove_node
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memcpy_using_uint64.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override_no_op.c
PROOF_SOURCES += $(PROOF_STUB)/s_sift_either_override.c
PROOF_SOURCES += $(PROOF_STUB)/aws_array_list_swap_override.c

PROJECT_SOURCES += $(SRCDIR)/source/array_list.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/priority_queue.c

REMOVE_FUNCTION_BODY +=  __CPROVER_file_local_priority_queue_c_s_sift_either
REMOVE_FUNCTION_BODY +=  aws_array_list_swap_override

###########

include ../Makefile.common
