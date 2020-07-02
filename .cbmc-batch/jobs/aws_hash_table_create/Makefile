# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# 2: 2m30s
# 4: 3m30s
MAX_TABLE_SIZE ?= 4
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

UNWINDSET +=__CPROVER_file_local_hash_table_c_s_find_entry1.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))
UNWINDSET += __CPROVER_file_local_hash_table_c_s_emplace_item.0:$(shell echo $$((1 + $$(( 2 * $(MAX_TABLE_SIZE) )) )) )

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override_no_op.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ABSTRACTIONS +=  $(HELPERDIR)/stubs/s_emplace_item_override.c
ABSTRACTIONS +=  $(HELPERDIR)/stubs/s_expand_table_override.c

ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body __CPROVER_file_local_hash_table_c_s_emplace_item
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body __CPROVER_file_local_hash_table_c_s_expand_table
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body nondet-compare

ENTRY = aws_hash_table_create_harness
###########

include ../Makefile.common
