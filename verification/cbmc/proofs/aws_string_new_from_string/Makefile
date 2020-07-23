# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include ../Makefile.aws_string

CBMCFLAGS +=

HARNESS_ENTRY = aws_string_new_from_string_harness
HARNESS_FILE = $(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROOF_SOURCES += $(PROOF_SOURCE)/proof_allocators.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/string.c

include ../Makefile.common
