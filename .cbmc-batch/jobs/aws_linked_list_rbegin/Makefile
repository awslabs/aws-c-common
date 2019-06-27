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

# Run deep validity checks in linked_list_is_valid
AWS_DEEP_CHECKS = 1

include ../Makefile.aws_linked_list

UNWINDSET += aws_linked_list_is_valid_deep.0:$(shell echo $$((2 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))
UNWINDSET += ensure_linked_list_is_allocated.0:$(shell echo $$((1 + $(MAX_LINKED_LIST_ITEM_ALLOCATION))))

CBMCFLAGS +=

DEPENDENCIES += $(HELPERDIR)/source/make_common_data_structures.c
DEPENDENCIES += $(HELPERDIR)/source/proof_allocators.c
DEPENDENCIES += $(HELPERDIR)/source/utils.c
DEPENDENCIES += $(HELPERDIR)/stubs/error.c

ENTRY = aws_linked_list_rbegin_harness
###########

include ../Makefile.common
