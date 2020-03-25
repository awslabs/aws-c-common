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

# Sufficently long to get full coverage on the aws_array_list APIs
# short enough that all proofs complete quickly
MAX_ITEM_SIZE ?= 2

# Necessary to get full coverage when using functions from math.h
MAX_INITIAL_ITEM_ALLOCATION ?= 9223372036854775808ULL

DEFINES += -DMAX_ITEM_SIZE=$(MAX_ITEM_SIZE)
DEFINES += -DMAX_INITIAL_ITEM_ALLOCATION=$(MAX_INITIAL_ITEM_ALLOCATION)
