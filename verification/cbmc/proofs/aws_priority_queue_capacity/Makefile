# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list

# This is the minimum bound to reach full coverage rate
UNWINDSET += memset_impl.0:41

CBMCFLAGS +=

PROOF_UID = aws_priority_queue_capacity
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override.c

PROJECT_SOURCES += $(SRCDIR)/source/priority_queue.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c

###########

include ../Makefile.common
