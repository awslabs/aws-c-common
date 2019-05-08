# Copyright 2019 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
#NOTE: Sufficient for full coverage
#16: 4s
#64: 5s
#128 10s
#256 53s
MAX_STRING_LEN ?= 128
DEFINES += -DMAX_STRING_LEN=$(MAX_STRING_LEN) 

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c
DEPENDENCIES += $(SRCDIR)/source/string.c

ENTRY = aws_hash_callback_string_destroy_harness

###########

include ../Makefile.common
