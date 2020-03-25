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
# Max needs to be big enough to have multiple loop unrollings to have full coverage
# 160 is well larger than that, and still completes quite fast: ~ 40s
MAX = 160
DEFINES += -DMAX=$(MAX)
UNWINDSET += memset_impl.0:$(shell echo $$(($(MAX) + 1)))
UNWINDSET += memset_using_uint64_impl.0:$(shell echo $$(( $$(( $(MAX) / 8 )) + 1)))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_override.c
DEPENDENCIES += $(HELPERDIR)/stubs/memset_using_uint64.c

ENTRY = memset_using_uint64_harness

###########

include ../Makefile.common
