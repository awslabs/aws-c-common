# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
MAX_CURSOR_SIZE ?= 32
DEFINES += -DMAX_CURSOR_SIZE=$(MAX_CURSOR_SIZE)

UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.0:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.1:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )
UNWINDSET += __CPROVER_file_local_lookup3_inl_hashlittle2.2:$(shell echo $$(( $$(( $(MAX_CURSOR_SIZE) / 12 )) +1 )) )

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_byte_cursor_ptr_harness
###########

include ../Makefile.common
