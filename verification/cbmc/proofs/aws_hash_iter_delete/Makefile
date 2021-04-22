# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

#4: 4m40s (smallest size that gives full coverage)
MAX_TABLE_SIZE ?= 4
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

CBMCFLAGS +=

PROOF_UID = aws_hash_iter_delete
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c
PROOF_SOURCES += $(PROOF_STUB)/s_remove_entry_override.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

REMOVE_FUNCTION_BODY += __CPROVER_file_local_hash_table_c_s_remove_entry

include ../Makefile.common
