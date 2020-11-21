# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#32: 4s
#64: 5s
#128 6s
#256 11s
#1024: 2m 30s
MAX_STRING_SIZE ?= 32
DEFINES += -DMAX_STRING_SIZE=$(MAX_STRING_SIZE)

UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.0:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.1:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.2:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )

CBMCFLAGS +=

PROOF_UID = aws_hash_string
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c
PROJECT_SOURCES += $(SRCDIR)/source/string.c

###########

include ../Makefile.common
