# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

include ../Makefile.aws_linked_list

## This has to take into account that a new element has been added to
## the list afterwards so we have to unwind one more time (instead of
## the standard 2 + MAX_LINKED_LIST_ITEM_ALLOCATION)
UNWINDSET += aws_linked_list_is_valid_deep.0:$(shell echo $$((3 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))
UNWINDSET += ensure_linked_list_is_allocated.0:$(shell echo $$((1 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c

ENTRY = aws_linked_list_push_back_harness
###########

include ../Makefile.common
