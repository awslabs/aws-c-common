# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
#NOTE: If we don't use the unwindset, leave it empty
#CBMC_UNWINDSET =

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_mul_size_saturating_harness
###########

include ../Makefile.common
