# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list

###########
#
# Runtime: 1200s

# This is the minimum bound to reach full coverage rate
UNWINDSET +=

CBMCFLAGS +=

PROOF_UID = aws_priority_queue_push
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memcpy_override_no_op.c
PROOF_SOURCES += $(PROOF_STUB)/s_sift_up_override.c

PROJECT_SOURCES += $(SRCDIR)/source/array_list.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/priority_queue.c

REMOVE_FUNCTION_BODY +=  __CPROVER_file_local_priority_queue_c_s_sift_up

###########

include ../Makefile.common
