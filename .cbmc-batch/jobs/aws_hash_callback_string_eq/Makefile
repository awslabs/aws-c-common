# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: Sufficient for full coverage
#32: 6
#64: 15s
#96: 1m
#128 2m 10s
MAX_STRING_LEN ?= 96
DEFINES += -DMAX_STRING_LEN=$(MAX_STRING_LEN) 

UNWINDSET +=memcmp.0:$(shell echo $$(($(MAX_STRING_LEN) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcmp_override.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c
DEPENDENCIES += $(SRCDIR)/source/string.c


ENTRY = aws_hash_callback_string_eq_harness

###########

include ../Makefile.common
