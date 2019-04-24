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
# Sufficient for coverage for bounded inputs
# Additional coverage is given using the -unbounded version of this proof
# Runtime aprox 5 min at this size.
MAX_TABLE_SIZE ?= 4
DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE) 

#A hash entry is 24 bytes, which is 3 iters. So we need 3 * MAX_TABLE_SIZE + 1
UNWINDSET += memset_override_0_impl.0:$(shell echo $$(($$((3 * $(MAX_TABLE_SIZE))) + 1)))

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override_0.c
DEPENDENCIES += $(SRCDIR)/source/common.c
DEPENDENCIES += $(SRCDIR)/source/hash_table.c

ENTRY = aws_hash_table_init_bounded_harness
###########

include ../Makefile.common
