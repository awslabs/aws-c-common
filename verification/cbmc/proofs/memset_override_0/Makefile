# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# Max needs to be big enough to have multiple loop unrollings to have full coverage
# 160 is well larger than that, and still completes quite fast: ~ 40s
MAX = 160
DEFINES += -DMAX=$(MAX)

UNWINDSET += memset_impl.0:$(shell echo $$(($(MAX) + 1)))
UNWINDSET += memset_override_0_impl.0:$(shell echo $$(( $$(( $(MAX) / 8 )) + 1)))

CBMCFLAGS +=

PROOF_UID = memset_override_0
HARNESS_ENTRY = $(PROOF_UID)_harness
HARNESS_FILE = $(PROOFDIR)/$(HARNESS_ENTRY).c

PROOF_SOURCES += $(HARNESS_FILE)
PROOF_SOURCES += $(PROOF_SOURCE)/utils.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override.c
PROOF_SOURCES += $(PROOF_STUB)/memset_override_0.c

# The actual implementation that we're proving comes from .inl files
# that the stubs pull in. Link against an empty file, since we're not
# using any other files in the project.
PROJECT_SOURCES += $(PROOF_STUB)/empty-source-file.c

###########

include ../Makefile.common
