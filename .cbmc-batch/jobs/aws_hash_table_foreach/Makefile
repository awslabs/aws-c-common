# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#4: 25s
#16: 10s
#32: 1m10s
MAX_TABLE_SIZE ?= 16
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

UNWINDSET +=  aws_hash_table_foreach.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ABSTRACTIONS += $(HELPERDIR)/stubs/aws_hash_iter_overrides.c
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body aws_hash_iter_begin
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body aws_hash_iter_delete
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body aws_hash_iter_done
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body aws_hash_iter_next

ENTRY = aws_hash_table_foreach_harness
###########

include ../Makefile.common
