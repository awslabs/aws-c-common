# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list

###########
#
# Runtime: 180s

# This is the minimum bound to reach full coverage rate
UNWINDSET += __CPROVER_file_local_array_list_c_aws_array_list_mem_swap.0:$(shell echo $$(($(MAX_ITEM_SIZE) + 1)))
UNWINDSET += memcpy_impl.0:$(shell echo $$(($(MAX_ITEM_SIZE) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_override.c
DEPENDENCIES += $(SRCDIR)/source/array_list.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/priority_queue.c


ENTRY = aws_priority_queue_s_swap_harness
###########

include ../Makefile.common
