# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: If we don't use the unwindset, leave it empty
#CBMC_UNWINDSET =

HARNESS_ENTRY = aws_add_size_checked_harness
HARNESS_FILE = $(HARNESS_ENTRY).c

CBMCFLAGS +=

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/common.c

###########

include ../Makefile.common
