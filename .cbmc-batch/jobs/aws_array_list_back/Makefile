# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list

# This bound allows us to reach 100% coverage rate
UNWINDSET += memcpy_impl.0:$(shell echo $$(($(MAX_ITEM_SIZE) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/array_list.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_array_list_back_harness
###########

include ../Makefile.common
