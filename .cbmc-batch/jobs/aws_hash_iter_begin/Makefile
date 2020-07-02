# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#16: 6 seconds
#32: 10s
#128: 2m 45s
MAX_TABLE_SIZE ?= 32
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

UNWINDSET +=  __CPROVER_file_local_hash_table_c_s_get_next_element.0:$(shell echo $$((1 + $(MAX_TABLE_SIZE))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_iter_begin_harness
###########

include ../Makefile.common
