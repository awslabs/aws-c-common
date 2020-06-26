# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#32: 4s
#64: 5s
#128 6s
#256 11s
#1024: 2m 30s
MAX_STRING_SIZE ?= 32
DEFINES += -DMAX_STRING_SIZE=$(MAX_STRING_SIZE) 

UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.0:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.1:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.2:$(shell echo $$(( $$(( $(MAX_STRING_SIZE) / 12 )) +1 )) )

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c
DEPENDENCIES += $(SRCDIR)/source/string.c

ENTRY = aws_hash_string_harness
###########

include ../Makefile.common
