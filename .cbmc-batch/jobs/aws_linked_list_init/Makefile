# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

# The loops have to be unwinded as many times as the elements of the
# list + 2. In this case, aws_linked_list_init returns an empty list
# so it is just 2.
UNWINDSET += aws_linked_list_is_valid_deep.0:2

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c

ENTRY = aws_linked_list_init_harness
###########

include ../Makefile.common
