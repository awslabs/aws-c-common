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

##########
MAX_TABLE_SIZE ?= 4

DEFINES += -DMAX_TABLE_SIZE=$(MAX_TABLE_SIZE)

#A table has 10 words for the struct, plus 3 words for each entry
TABLE_SIZE_IN_WORDS=$(shell echo $$(($$((3 * $(MAX_TABLE_SIZE))) + 10)))
