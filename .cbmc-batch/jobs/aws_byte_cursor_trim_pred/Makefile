# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0.

###########
include ../Makefile.aws_byte_buf

UNWINDSET += aws_byte_cursor_left_trim_pred.0:$(shell echo $$(($(MAX_BUFFER_SIZE) + 1)))
UNWINDSET += aws_byte_cursor_right_trim_pred.0:$(shell echo $$(($(MAX_BUFFER_SIZE) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(SRCDIR)/source/byte_buf.c
DEPENDENCIES += $(SRCDIR)/source/common.c

ENTRY = aws_byte_cursor_trim_pred_harness
###########

include ../Makefile.common
