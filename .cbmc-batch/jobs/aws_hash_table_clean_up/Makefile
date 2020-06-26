# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#4: 60s
#8: 1m50s
#16: 6m30s
MAX_TABLE_SIZE ?= 8

include ../Makefile.aws_hash_table

UNWINDSET += aws_hash_table_clear.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_table_clean_up_harness
###########

include ../Makefile.common
