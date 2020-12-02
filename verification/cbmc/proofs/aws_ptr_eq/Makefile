# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

CBMCFLAGS +=

PROOF_UID = aws_ptr_eq
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)

PROJECT_SOURCES += $(SRCDIR)/source/hash_table.c

###########

include ../Makefile.common
