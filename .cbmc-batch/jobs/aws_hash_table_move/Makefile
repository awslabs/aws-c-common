# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_table_move_harness
###########

include ../Makefile.common
