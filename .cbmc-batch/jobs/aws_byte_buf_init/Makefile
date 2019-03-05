# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
#
# Licensed under the Apache License, Version 2.0 (the "License"). You may not use
# this file except in compliance with the License. A copy of the License is
# located at
#
#     http://aws.amazon.com/apache2.0/
#
# or in the "license" file accompanying this file. This file is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
# implied. See the License for the specific language governing permissions and
# limitations under the License.

###########
#NOTE: If we don't use the unwindset, leave it empty
#CBMC_UNWINDSET = --unwindset

CBMCFLAGS +=

DEPENDENCIES = $(SRCDIR)/source/array_list.c \
	       $(SRCDIR)/source/byte_buf.c \
	       $(SRCDIR)/source/common.c \
	       $(SRCDIR)/source/error.c

ENTRY = aws_byte_buf_init_harness
###########

include ../Makefile.common
