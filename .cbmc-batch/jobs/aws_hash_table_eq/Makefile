# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# 8: 2m30s
MAX_TABLE_SIZE ?= 8
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

UNWINDSET +=  aws_hash_table_eq.3:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ABSTRACTIONS += $(HELPERDIR)/stubs/aws_hash_table_find_override.c

ADDITIONAL_REMOVE_FUNCTION_BODY +=  --remove-function-body aws_hash_table_find

ENTRY = aws_hash_table_eq_harness
###########

include ../Makefile.common
