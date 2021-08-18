# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: Sufficient for full coverage
#16: 4s
#64: 14s
#128 1m40ss
MAX_STRING_LEN ?= 64
DEFINES += -DMAX_STRING_LEN=$(MAX_STRING_LEN)

UNWINDSET += strcmp.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))
UNWINDSET += strlen.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))

CBMCFLAGS +=

PROOF_UID = aws_hash_callback_c_str_eq
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c
PROJECT_SOURCES += $(SRCDIR)/source/string.c



###########

include ../Makefile.common
