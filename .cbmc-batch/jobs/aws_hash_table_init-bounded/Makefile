# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# Using the new calloc model, get full coverage in about 5s on unbounded sizes!
MAX_TABLE_SIZE ?= SIZE_MAX
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body bounded_malloc
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body can_fail_malloc
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body nondet_compare
ADDITIONAL_REMOVE_FUNCTION_BODY += --remove-function-body s_can_fail_malloc_allocator

ENTRY = aws_hash_table_init_bounded_harness
###########

include ../Makefile.common
