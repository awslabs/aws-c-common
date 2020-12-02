# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: Sufficient for full coverage
#32: 6
#64: 15s
#96: 1m
#128 2m 10s
MAX_STRING_LEN ?= 96
DEFINES += -DMAX_STRING_LEN=$(MAX_STRING_LEN)

UNWINDSET +=memcmp.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))

CBMCFLAGS +=

PROOF_UID = aws_hash_callback_string_eq
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/memcmp_override.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c
PROJECT_SOURCES += $(SRCDIR)/source/string.c



###########

include ../Makefile.common
