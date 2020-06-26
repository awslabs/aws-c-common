# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#4: 35s
#8: 1m10s
#16: 6m30s
MAX_TABLE_SIZE ?= 4

include ../Makefile.aws_hash_table

UNWINDSET += aws_hash_table_clear.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))
UNWINDSET += memset_override_0_impl.0:$(shell echo $$((1 + $(TABLE_SIZE_IN_WORDS))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override_0.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_table_clear_harness
###########

include ../Makefile.common
