# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

include ../Makefile.aws_string

UNWINDSET += memcmp.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(SRCDIR)/source/array_list.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/error.c
DEPENDENCIES += $(SRCDIR)/source/string.c

ENTRY = aws_array_list_comparator_string_harness

include ../Makefile.common
