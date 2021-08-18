# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include ../Makefile.aws_string

UNWINDSET += memcmp.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))
UNWINDSET += aws_array_eq_ignore_case.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))

CBMCFLAGS +=

PROOF_UID = aws_string_eq_byte_buf_ignore_case
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROJECT_SOURCES += $(SRCDIR)/source/byte_buf.c
PROJECT_SOURCES += $(SRCDIR)/source/common.c
PROJECT_SOURCES += $(SRCDIR)/source/error.c
PROJECT_SOURCES += $(SRCDIR)/source/string.c

include ../Makefile.common
