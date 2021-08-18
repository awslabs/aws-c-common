# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
MAX_CURSOR_SIZE ?= 32
DEFINES += -DMAX_CURSOR_SIZE=$(MAX_CURSOR_SIZE)

UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.0:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.1:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.2:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )

CBMCFLAGS +=

PROOF_UID = aws_hash_byte_cursor_ptr
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

###########

include ../Makefile.common
