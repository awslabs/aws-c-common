# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

include ../Makefile.aws_linked_list

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

UNWINDSET += aws_linked_list_is_valid_deep.0:$(shell echo $$((2 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))
UNWINDSET += ensure_linked_list_is_allocated.0:$(shell echo $$((1 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c

ENTRY = aws_linked_list_begin_harness
###########

include ../Makefile.common
