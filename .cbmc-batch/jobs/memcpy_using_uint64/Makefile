# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
# Max needs to be big enough to have multiple loop unrollings to have full coverage
# 160 is well larger than that, and still completes quite fast: ~ 40s
MAX = 160
DEFINES += -DMAX=$(MAX)

UNWINDSET += memcpy_impl.0:$(shell echo $$(($(MAX) + 1)))
UNWINDSET += memcpy_using_uint64_impl.0:$(shell echo $$(( $$(( $(MAX) / 8 )) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_override.c
DEPENDENCIES += $(HELPERDIR)/stubs/memcpy_using_uint64.c

ENTRY = memcpy_using_uint64_harness

###########

include ../Makefile.common
