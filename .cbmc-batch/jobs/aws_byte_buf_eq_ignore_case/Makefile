# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_byte_buf

UNWINDSET += memcmp.0:$(shell echo $$(($(MAX_BUFFER_SIZE) + 1)))
UNWINDSET += aws_array_eq_ignore_case.0:$(shell echo $$(($(MAX_BUFFER_SIZE) + 1)))


CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcmp_override.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_byte_buf_eq_ignore_case_harness
###########

include ../Makefile.common
