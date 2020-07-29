# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_array_list

# This bound allow us to reach full coverage rate
UNWINDSET += memset_impl.0:41

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override.c
DEPENDENCIES += $(SRCDIR)/source/priority_queue.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_priority_queue_init_dynamic_harness
###########

include ../Makefile.common
