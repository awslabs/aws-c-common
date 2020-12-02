# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#4: 35s
#8: 1m10s
#16: 6m30s
MAX_TABLE_SIZE ?= 4

include ../Makefile.aws_hash_table

UNWINDSET += aws_hash_table_clear.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))
UNWINDSET += memset_override_0_impl.0:$(shell echo $$((1 + $(TABLE_SIZE_IN_WORDS))))

CBMCFLAGS +=

PROOF_UID = aws_hash_table_clear
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override_0.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

###########

include ../Makefile.common
