# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: Sufficient for full coverage
#16: 4s
#64: 5s
#128 10s
#256 53s
MAX_STRING_LEN ?= 128
DEFINES += -DMAX_STRING_LEN=$(MAX_STRING_LEN) 

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c
DEPENDENCIES += $(SRCDIR)/source/string.c

ENTRY = aws_hash_callback_string_destroy_harness

###########

include ../Makefile.common
