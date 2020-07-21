# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
CBMCFLAGS +=

HARNESS_ENTRY = aws_is_power_of_two_harness
HARNESS_FILE = $(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)

# The actual implementation that we're proving comes from .inl files
# that the stubs pull in. Link against an empty file, since we're not
# using any other files from c-common.
PROJECT_SOURCES += $(PROOF_STUB)/empty-source-file.c

###########

include ../Makefile.common
