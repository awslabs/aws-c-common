# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# 8: 2m30s
MAX_TABLE_SIZE ?= 8
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

UNWINDSET +=  aws_hash_table_eq.3:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

PROOF_UID = aws_hash_table_eq
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/aws_hash_table_find_override.c
PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

REMOVE_FUNCTION_BODY +=  aws_hash_table_find

###########

include ../Makefile.common
