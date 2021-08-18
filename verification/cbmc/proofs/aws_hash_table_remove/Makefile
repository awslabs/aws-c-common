# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# 2: 2m30s
# 4: 3m30s
MAX_TABLE_SIZE ?= 4
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

UNWINDSET +=__CPROVER_file_local_hash_table_c_s_find_entry1.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

PROOF_UID = aws_hash_table_remove
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override_no_op.c
PROOF_SOURCES += $(PROOF_STUB)/s_emplace_item_override.c
PROOF_SOURCES += $(PROOF_STUB)/s_expand_table_override.c
PROOF_SOURCES += $(PROOF_STUB)/s_remove_entry_override.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

REMOVE_FUNCTION_BODY +=  __CPROVER_file_local_hash_table_c_s_emplace_item
REMOVE_FUNCTION_BODY +=  __CPROVER_file_local_hash_table_c_s_expand_table
REMOVE_FUNCTION_BODY += __CPROVER_file_local_hash_table_c_s_remove_entry

include ../Makefile.common
