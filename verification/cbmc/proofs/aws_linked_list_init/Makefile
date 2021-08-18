# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

# The loops have to be unwinded as many times as the elements of the
# list + 2. In this case, aws_linked_list_init returns an empty list
# so it is just 2.
UNWINDSET += __CPROVER_file_local_linked_list_inl_aws_linked_list_is_valid_deep.0:2

CBMCFLAGS +=

PROOF_UID = aws_linked_list_init
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
