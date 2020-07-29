# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_byte_buf

MAX_BUFFER_SIZE=40

# This bound allows us to reach 100% coverage rate
UNWINDSET += memset_impl.0:$(shell echo $$(($(MAX_BUFFER_SIZE) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_byte_buf_clean_up_secure_harness
###########

include ../Makefile.common
