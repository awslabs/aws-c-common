# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

include ../Makefile.aws_linked_list

## This has to take into account that a new element has been added to
## the list afterwards so we have to unwind one more time (instead of
## the standard 2 + MAX_LINKED_LIST_ITEM_ALLOCATION)
UNWINDSET += __CPROVER_file_local_linked_list_inl_aws_linked_list_is_valid_deep.0:$(shell echo $$((3 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))
UNWINDSET += ensure_linked_list_is_allocated.0:$(shell echo $$((1 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))

CBMCFLAGS +=

PROOF_UID = aws_linked_list_push_front
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/make_common_data_structures.c
PROJECT_SOURCES += $(SRCDIR)/source/allocator.c
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c

PROOF_SOURCES += $(PROOF_STUB)/error.c

# The actual implementation that we're proving comes from .inl files
# that the stubs pull in. Link against an empty file, since we're not
# using any other files from c-common.
PROJECT_SOURCES += $(PROOF_STUB)/empty-source-file.c

###########

include ../Makefile.common
