# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#4: 25s
#8: 1m
#16: 5m45s
MAX_TABLE_SIZE ?= 8
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

UNWINDSET +=  __CPROVER_file_local_hash_table_c_s_find_entry1.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

PROOF_UID = aws_hash_table_find
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

###########

include ../Makefile.common
