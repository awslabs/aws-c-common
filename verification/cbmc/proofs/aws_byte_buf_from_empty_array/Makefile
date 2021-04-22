# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
UNWINDSET +=

CBMCFLAGS +=

PROOF_UID = aws_byte_buf_from_empty_array
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c

###########

include ../Makefile.common
