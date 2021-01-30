# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# Using the new calloc model, get full coverage in about 5s on unbounded sizes!
MAX_TABLE_SIZE ?= SIZE_MAX
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

PROOF_UID = aws_hash_table_init_bounded
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

REMOVE_FUNCTION_BODY +=  bounded_malloc
REMOVE_FUNCTION_BODY +=  can_fail_malloc
REMOVE_FUNCTION_BODY +=  nondet_compare
REMOVE_FUNCTION_BODY +=  s_can_fail_malloc_allocator

###########

include ../Makefile.common
