# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list
include ../Makefile.aws_priority_queue_sift

###########
#
# Runtime:
# - 300s for MAX_PRIORITY_QUEUE_ITEMS=3 items

# Note:
# In order to reach full coverage we need to unwind the harness loop
# as many times as the number of queue items, and the sift down loop
# log(NUMBER_PRIO_QUEUE_ITEMS) times.
UNWINDSET += __CPROVER_file_local_priority_queue_c_s_sift_down.0:$(MAX_HEAP_HEIGHT)
UNWINDSET += __CPROVER_file_local_priority_queue_c_s_sift_up.0:$(MAX_HEAP_HEIGHT)
UNWINDSET += aws_priority_queue_s_sift_either_harness.0:$(shell echo $$((1 + $(MAX_PRIORITY_QUEUE_ITEMS))))
UNWINDSET += aws_priority_queue_backpointers_valid_deep.0:$(shell echo $$((1 + $(MAX_PRIORITY_QUEUE_ITEMS))))

CBMCFLAGS +=

PROOF_UID = aws_priority_queue_s_sift_either
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memcpy_override_havoc.c
PROOF_SOURCES += $(PROOF_STUB)/s_swap_override_no_op.c

PROJECT_SOURCES += $(SRCDIR)/source/array_list.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/priority_queue.c

REMOVE_FUNCTION_BODY +=  __CPROVER_file_local_priority_queue_c_s_swap

###########

include ../Makefile.common

